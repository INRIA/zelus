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

let debug = ref false

let log_info s i =
  if !debug then begin print_string s; print_float i; print_newline () end
					   
type status =
  | Interpolate (* no integration was necessary *)
  | Success of float (* the integration succeed; limit time for correctness *)
  | RootsFound (* a root has been found *)
  | Horizon of float (* the integration has succeed; returns the next horizon *)
  | Cascade (* a cascade *)
  | StopTimeReached (* the end of simulation time is reached *)
  | TimeHasPassed (* an output at time [h] is expected but *)
                  (* [h < start] where [start] *)
                  (* is the last restart time of the solver *)
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
	 mutable t_start: float;
	 (* time of the previous reset or mesh point *)
	 mutable t_limit: float;
	 (* time for the limit of the next solver step, i.e., next time event *)
	 mutable t_mesh: float;
	 (* time reached by the solver. No zero-crossing in [t_start, t_mesh] *)
	 mutable input: 'a; (* the input is read at discrete-time instants *)
	 mutable output: 'b; (* the current output *)
	 mutable next: simulation_state; (* state of the simulation *)
       }

     and simulation_state =
       | Integrate (* integrate the signal *)
       | Discrete of bool (* true means zero-crossing; false a cascade *)
       | End (* end of the simulation; stop_time has been reached *)
							
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
      let crossing s input time cvec zoutvec =
	cstate.major <- false;
	cstate.zinvec <- no_roots_in;
	cstate.dvec <- ignore_der;
	cstate.zoutvec <- zoutvec;
	cstate.cvec <- cvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	ignore (f_step s (no_time, input)) in

      (* the function which compute the output during integration *)
      let output s input cvec =
	cstate.major <- false;
	cstate.zoutvec <- no_roots_out;
	cstate.dvec <- ignore_der;
	cstate.zinvec <- no_roots_in;
	cstate.cvec <- cvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	f_step s (no_time, input) in

      (* the function which sets the zinvector into the *)
      (* internal zero-crossing variables *)
      let setroots s input cvec zinvec =
	cstate.major <- false;
	cstate.zoutvec <- no_roots_out;
	cstate.dvec <- ignore_der;
	cstate.zinvec <- zinvec;
	cstate.cvec <- cvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	ignore (f_step s (no_time, input)) in

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
	  | Running { zstate; sstate; t_mesh } ->
	     SSolver.reinitialize sstate t_mesh nvec;
	     ZSolver.reinitialize zstate t_mesh cvec in

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
		 ZSolver.initialize n_zeros (crossing state input) cvec in
	       SSolver.set_stop_time sstate stop_time;
	       
	       if cstate.horizon = 0.0 then
		 let solver =
		   { sstate = sstate; zstate = zstate;
		     t_start = 0.0; t_limit = 0.0; t_mesh = 0.0; input = input;
		     output = result; next = Discrete(false) } in
		 s.solver <- Running solver;
		 log_info "horizon = " 0.0;
		 { time = 0.0; status = Cascade; result = result }
	       else
		 if stop_time <= 0.0 then
		   let solver =
		     { sstate = sstate; zstate = zstate; 
		       t_start = 0.0; t_limit = 0.0; t_mesh = 0.0;
		       input = input; output = result;
		       next = End } in
		   s.solver <- Running solver;
		   log_info "horizon = " 0.0;
		   { time = 0.0; status = StopTimeReached; result = result }
		 else
		   let t_limit =
		     min stop_time cstate.horizon in
		   let solver =
		     { sstate = sstate; zstate = zstate;
		       t_start = 0.0; t_limit = t_limit; t_mesh = 0.0;
		       input = input; output = result; next = Integrate } in
		   s.solver <- Running solver;
		   log_info "t_limit = " t_limit;
		   { time = 0.0; status = Horizon(t_limit);
		     result = result }
	    | Running({ next; sstate; zstate; t_start; t_mesh; t_limit } as s)
	      ->
	       (* time has passed *)
	       if horizon < t_start then
		 { time = t_start; status = TimeHasPassed; result = s.output }
	       else
		 (* interpolate the state at that instant *)
		 (* compute the current output *)
		 if horizon <= t_mesh
		 then
		   let _ = SSolver.get_dky sstate nvec horizon 0 in
		   let result = output state input cvec in
		   s.output <- result;
		   { time = horizon; status = Interpolate; result = result }
		 else
	    	   match next with
		   | Discrete(is_zero_crossing) ->
		      log_info "StepRootsFound or StepCascade: time = " t_mesh;
		      if is_zero_crossing
		      then setroots state input cvec roots;
		      let result = majorstep state t_mesh cvec input in
		      s.output <- result;
		      let status =
			if cstate.horizon = 0.0
			then begin s.next <- Discrete(false); Cascade end
			else
			  let t_limit = min stop_time cstate.horizon in
		     	  let _ = SSolver.reinitialize sstate t_mesh nvec in
			  let _ = ZSolver.reinitialize zstate t_mesh cvec in
			  s.t_start <- t_mesh;
			  s.t_limit <- t_limit;
			  s.next <- Integrate;
			  Horizon(t_limit) in
		      { time = t_mesh; status = status; result = s.output }
		   | Integrate ->
		      log_info "Integrate: t_mesh = " t_mesh;
		      if t_mesh >= stop_time then
			begin
			  s.next <- End;
			  { time = stop_time; status = StopTimeReached;
			    result = s.output }
			end
		      else
			let t_nextmesh =
			  (* integrate *)
			  SSolver.step sstate (add_margin t_limit) nvec in
			(* interpolate if the mesh point has passed the *)
			(* time limit *)
 			log_info "t_nextmesh = " t_nextmesh;
			let t =
			  if t_limit < t_nextmesh
			  then (SSolver.get_dky sstate nvec t_limit 0; t_limit)
			  else t_nextmesh in
			log_info "t_nextmesh = " t;
			(* is there a zero-crossing? *)
			ZSolver.step zstate t cvec;
			let has_roots = ZSolver.has_roots zstate in
			let status =
			  if has_roots then
			    let t =
			      ZSolver.find
				zstate (SSolver.get_dky sstate nvec, cvec)
				roots in
			    s.t_mesh <- t;
			    s.next <- Discrete(true);
			    Success(t)
			  else
			    let next =
			      if t = t_limit then Discrete(false)
			      else Integrate in
			    s.t_mesh <- t;
			    s.next <- next;
			    Success(t) in			    
			{ time = s.t_start; status = status; result = s.output }
		   | End ->
		      log_info "End: t_mesh = " stop_time;
		      { time = s.t_start; status = StopTimeReached;
			result = s.output }
	  with
	  | x -> raise x in
	Node { alloc = alloc; step = step; reset = reset }
  end
    
module Solver = Make (Sundials_cvode) (Illinois)
		     
let solve = Solver.solve 

