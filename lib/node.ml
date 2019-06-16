(**************************************************************************)
(*                                                                        *)
(*                                Zelus                                   *)
(*               A synchronous language for hybrid systems                *)
(*                       http://zelus.di.ens.fr                           *)
(*                                                                        *)
(*                    Marc Pouzet and Timothy Bourke                      *)
(*                                                                        *)
(*  Copyright 2012 - 2019. All rights reserved.                           *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(*  Zelus is developed in the INRIA PARKAS team.                          *)
(*                                                                        *)
(**************************************************************************)

(* This module provides functions for lifting a hybrid function into *)
(* a discrete one. This is the so-called "co-simulation" of a *)
(* continuous or hybrid model in which the numerical solver *)
(* and zero-crossing detection mechanism are embedded into the step function *)

(* Lift a hybrid node into a discrete node *)
(* [solve f stop_time (input, t) = next_t, result]
   - f : 'a -C-> 'b is the hybrid node;
   - stop_time : float is the stop time (end) of the simulation;
   - input : 'a is a stream;
   - t : float is a stream of horizons that must be increasing
   (forall n in Nat. t(n) <= t(n+1))
   - result : 'b return is a stream of results;
   - next_t : float is a stream of achieved horizons *)
    
(* compile with:
 *- ocamlfind ocamlc bigarray.cma sundials.cma ztypes.ml node.ml *)
(*- ocamlfind ocamlc bigarray.cma -package sundialsml sundials.cma
    zls.cmo -I solvers solvers/illinois.cmo solvers/sundials_cvode.cmo 
    ztypes.ml node.ml *)


open Ztypes
open Zlsolve

let debug = ref true

let log_info s i =
  if !debug then begin print_string s; print_float i; print_newline () end
					   
type status =
  | Success (* the integration has succeed *)
  | RootsFound (* a root has been found *)
  | Horizon of float (* the integration has succeed; returns the next horizon *)
  | Cascade (* a cascade *)
  | StopTimeReached (* the end of simulation time is reached *)
  | Error (* something went wrong during integration *)

type 'a return =
    { time: float; status: status; result: 'a }
      
module Make (SSolver: Zls.STATE_SOLVER) (ZSolver: Zls.ZEROC_SOLVER) =
  struct
    (* the state of the solver. Either never called (allocated) or running *)
    type ('a, 'b) solver =
      | Init (* initial state of the simulation *)
      | Running of ('a, 'b) solver_state
		     
     and ('a, 'b) solver_state =
       { zstate: ZSolver.t; (* the solver state *)
	 sstate: SSolver.t; (* the zero-crossing solver state *)
	 mutable start: float;  (* time at the start of a step *)
	 mutable limit: float; (* horizon for the next solver step *)
	 mutable input: 'a; (* the input is read at discrete-time instants *)
	 mutable output: 'b;
	               (* the output is returned at discrete-time instants *)
	 mutable next: simulation_state; (* state of the simulation *)
       }

     and simulation_state =
       | Integrate | StepRootsFound | StepCascade | StepStopTimeReached
							
    type ('a, 'b) state = { state: 'a; mutable solver: 'b }      
			    
    (* increment a given horizon by a small margin *)
    let add_margin h = h +. (2.0 *. epsilon_float *. h)

    (* the main lifting function *)
    let solve f (stop_time: float) =
      let cstate =
	{ cvec = Zls.cmake 0; dvec = Zls.cmake 0; cindex = 0; zindex = 0;
	  cend = 0; zend = 0; cmax = 0; zmax = 0;
	  zinvec = Zls.zmake 0; zoutvec = Zls.cmake 0;
	  major = false; horizon = stop_time } in

      (* create a node *)
      let Node { alloc = f_alloc; step = f_step; reset = f_reset } = f cstate in
      
      (* allocate the state of [f] *)
      let s = f_alloc () in
      
      let n_zeros = cstate.zmax in
      let n_cstates = cstate.cmax in

      let no_roots_in = Zls.zmake n_zeros in
      let no_roots_out = Zls.cmake n_zeros in
      let roots = Zls.zmake n_zeros in
      let nvec = SSolver.cmake n_cstates in
      let cvec = SSolver.unvec nvec in
      let ignore_der = Zls.cmake n_cstates in
      
      let no_time = -1.0 in
      
      (* the function that compute the derivatives *)
      let derivative s input time cvec dvec =
	cstate.major <- false;
	cstate.zinvec <- no_roots_in;
	cstate.zoutvec <- no_roots_out;
	cstate.cvec <- cvec;
	cstate.dvec <- dvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	ignore (f_step s (no_time, input)) in
  
      (* the function that compute the zero-crossings *)
      let zcrossing s input time cvec zoutvec =
	cstate.major <- false;
	cstate.zinvec <- no_roots_in;
	cstate.dvec <- ignore_der;
	cstate.zoutvec <- zoutvec;
	cstate.cvec <- cvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	ignore (f_step s (no_time, input)) in

      (* the function which compute the output *)
      let minorstep s time input cvec zinvec =
	cstate.major <- false;
	cstate.zoutvec <- no_roots_out;
	cstate.dvec <- ignore_der;
	cstate.zinvec <- zinvec;
	cstate.cvec <- cvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	ignore (f_step s (time, input)) in

      (* the function which compute a discrete step *)
      let majorstep s time cvec input =
	cstate.major <- true;
	cstate.horizon <- infinity;
	cstate.zinvec <- no_roots_in;
	cstate.zoutvec <- no_roots_out;
	cstate.dvec <- ignore_der;
	cstate.cvec <- cvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	f_step s (time, input) in

      (* the allocation function *)
      let alloc () =
	(* At this point, we do not allocate the solver states yet. *)
	(* this is due to the way we compile and will change once *)
	(* slicing is done to obtain an [f] (derivative) and [g] *)
	(* (zero-crossing) that do not need the [input] argument *)
	{ state = s; solver = Init } in
      
	let reset { state; solver } =
	  f_reset state;
	  match solver with
	  | Init -> ()
	  | Running { zstate; sstate; start } ->
	     SSolver.reinitialize sstate start nvec;
	     ZSolver.reinitialize zstate start cvec in

	(* the step function *)
	let step ({ state; solver } as s) (horizon, input) =
	  try
	    (* make a step *)
	    match solver with
	    | Init ->
	       log_info "Init: start = " 0.0;
	       (* initial major step *)
	       let result = majorstep state 0.0 cvec input in

	       (* Allocate the solver *)
	       let sstate =
		 SSolver.initialize (derivative state input) nvec in
	       (* Allocate the zsolver *)
	       let zstate =
		 ZSolver.initialize n_zeros (zcrossing state input) cvec in
	       SSolver.set_stop_time sstate stop_time;
	       
	       if cstate.horizon = 0.0 then
		 let solver =
		   { sstate = sstate; zstate = zstate;
		     start = 0.0; limit = 0.0; input = input;
		     output = result; next = StepCascade } in
		 s.solver <- Running solver;
		 log_info "horizon = " 0.0;
		 { time = 0.0; status = Cascade; result = result }
	       else
		 if stop_time <= 0.0 then
		   let solver =
		     { sstate = sstate; zstate = zstate; 
		       start = 0.0; limit = 0.0;
		       input = input; output = result;
		       next = StepStopTimeReached } in
		   s.solver <- Running solver;
		   log_info "horizon = " 0.0;
		   { time = 0.0; status = StopTimeReached; result = result }
		 else
		   let h = min stop_time (min horizon cstate.horizon) in
		   let solver =
		     { sstate = sstate; zstate = zstate;
		       start = 0.0; limit = h;
		       input = input; output = result; next = Integrate } in
		   s.solver <- Running solver;
		   log_info "horizon = " h;
		   { time = 0.0; status = Horizon(h);
		     result = result }
	    | Running ({ next = StepRootsFound; sstate; zstate; start } as s) ->
	       log_info "StepRootsFound: start = " start;
	       (* make a discrete step *)
	       let result = majorstep state start cvec input in
	       s.output <- result;
	       (* according to the horizon, either cascade or integration *)
	       let status =
		 if cstate.horizon = 0.0
		 then begin s.next <- StepCascade; Cascade end
		 else
		   let h = min stop_time (min horizon cstate.horizon) in
		   SSolver.reinitialize sstate start nvec;
		   ZSolver.reinitialize zstate start cvec;
		   s.limit <- h;
		   s.next <- Integrate;
		   Horizon(h) in
	       { time = s.start; status = status; result = s.output }
            | Running ({ next = StepCascade; zstate; sstate; start } as s) ->
	       log_info "StepCascade: start = " start;
	       (* make a discrete step *)
	       let result = majorstep state start cvec input in
	       s.output <- result;
	       let h = cstate.horizon in
	       log_info "horizon = " h;
	       (* according to the horizon, either cascade or integration *)
	       let status =
		 if h = 0.0
		 then begin s.next <- StepCascade; Cascade end
		 else
		   if start = stop_time then
		     begin
		       s.next <- StepStopTimeReached;
		       Horizon(stop_time)
		     end
		   else
		     let h = min stop_time h in
		     SSolver.reinitialize sstate start nvec;
		     ZSolver.reinitialize zstate start cvec;
		     s.limit <- min horizon h;
		     s.next <- Integrate;
		     Horizon(h) in
	       { time = s.start; status = status; result = s.output }  
	    | Running
		({ next = Integrate; zstate; sstate; start; limit } as s) ->
	       log_info "Integrate: start = " start;
	       let t_nextmesh = SSolver.step sstate (add_margin limit) nvec in
	       (* interpolate if the mesh point has passed the time limit *)
 	       log_info "t_nextmesh = " t_nextmesh;
	       let t = if limit < t_nextmesh
		       then (SSolver.get_dky sstate nvec limit 0; limit)
		       else t_nextmesh in
	       log_info "time = " t;
	       (* is there a zero-crossing? *)
	       ZSolver.step zstate t cvec;
	       let has_roots = ZSolver.has_roots zstate in
	       let status =
		 if has_roots then
		   let t =
		     ZSolver.find zstate (SSolver.get_dky sstate nvec, cvec)
				  roots in
		   (* one more step to actualize left limits *)
		   (* and the zero-crossing state variables *)
		   minorstep state t s.input cvec roots;
		   s.start <- t;
		   s.next <- StepRootsFound;
		   Success
		 else
		   if t >= limit then
		     begin
		       s.start <- t;
		       s.next <- StepCascade;
		       Success
		     end
		   else begin
		     s.start <- t;
                     s.next <- Integrate;
		     Success
		   end in
	       { time = s.start; status = status; result = s.output }
            | Running({ next = StepStopTimeReached } as s) ->
	       log_info "StepStopTimeReached" stop_time;
	       { time = s.start; status = StopTimeReached; result = s.output }
	  with
	  | x -> raise x in
	Node { alloc = alloc; step = step; reset = reset }
  end
    
module Solver = Make (Sundials_cvode) (Illinois)

let solve = Solver.solve 

