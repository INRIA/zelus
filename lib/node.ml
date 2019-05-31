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
(* a discrete one. This the so-called "co-simulation" of a *)
(* continuous or hybrid model in which the numerical solver *)
(* and zero-crossing detection mechanism is embedded into the step function *)

(* compile with:
 *- ocamlfind ocamlc bigarray.cma sundials.cma ztypes.ml node.ml *)
(*- ocamlfind ocamlc bigarray.cma -package sundialsml sundials.cma
    zls.cmo -I solvers solvers/illinois.cmo solvers/sundials_cvode.cmo 
    ztypes.ml node.ml *)
open Ztypes

type 'a simu =
  | SimInit (* initial state of the simulation *)
  | SimIntegration (* integrate the signals *)
  | SimDiscrete of 'a return (* make a step *)
      
and 'a return =
   | Success (* the integration has succeed; no step *)
   | RootsFound (* a root has been found *)
   | Horizon (* the integration has succeed; an horizon is reached *)
   | Cascade of 'a (* a cascade *)
   | StopTimeReached (* the end of simulation time is reached *)
   | Error (* something went wrong during integration *)
       
module Make (SSolver: Zls.STATE_SOLVER) (ZSolver: Zls.ZEROC_SOLVER) =
  struct
    (* the type that define the internal state of the node *)
    type ('a, 'b, 's) sstate =
	{ state: 's; (* the discrete state *)
	  zstate: ZSolver.t; (* the solver state *)
	  sstate: SSolver.t; (* the zero-crossing solver state *)
	  yinit_nvec: SSolver.nvec;
	                     (* the continuous state vector for the solver *)
	  mutable time: float;  (* the current time of the simulation *)
	  mutable simu: 'a simu; (* the current state of the simulation *)
	}
  
    let take = function | None -> assert false | Some(v) -> v

    (* Lift a hybrid node into a node *)
    (* [solve f stop_time (input, t) = next_t, result]
       - f : 'a -C-> 'b is the hybrid node;
       - stop_time : float is the stop time (end) of the simulation;
       - input : 'a is a stream;
       - t : float is a stream of horizons that must be increasing
             (forall n in Nat. t(n) <= t(n+1))
       - result : 'b return is a stream of results;
       - next_t : float is a stream of achieved horizons *)
    let solve f (stop_time: float) default =
      let cstate =
	{ cvec = Zls.cmake 0; dvec = Zls.cmake 0; cindex = 0; zindex = 0;
	  cend = 0; zend = 0; cmax = 0; zmax = 0;
	  zinvec = Zls.zmake 0; zoutvec = Zls.cmake 0;
	  major = false; horizon = stop_time } in

      let input = ref (Some(default)) in

      (* create a node *)
      let Node { alloc; step; reset } = f cstate in
      
      (* the derivative *)
      let f s time cvec dvec =
	cstate.major <- false;
	cstate.cvec <- cvec;
	cstate.dvec <- dvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	ignore (step s (time, take !input)) in
  
      (* the zero-crossing function *)
      let g s time cvec zoutvec =
	cstate.major <- false;
	cstate.cvec <- cvec;
	cstate.zoutvec <- zoutvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	ignore (step s (time, take !input)) in
  
      (* the minorstep function *)
      let minorstep s time =
	cstate.major <- false;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	step s (time, take !input) in

      (* the majorstep function *)
      let majorstep s time cvec i =
	cstate.major <- true;
	cstate.horizon <- infinity;
	cstate.cvec <- cvec;
	cstate.cindex <- 0;
	cstate.zindex <- 0;
	step s (time, i) in

      (* the alloc function *)
      let alloc () =
	(* allocate the discrete state of [f] *)
	let s = alloc () in

	(* the nvector used by the solver to store the continuous state *)
	let yinit_nvec = SSolver.cmake cstate.cmax in
	
	(* allocate the state vectors and zero-crossing vectors *)
	cstate.cvec <- SSolver.unvec yinit_nvec;
	cstate.dvec <- Zls.cmake cstate.cmax;
	cstate.zoutvec <- Zls.cmake cstate.zmax;
	cstate.zinvec <- Zls.zmake cstate.zmax;

	(* the solver state *)
	let sstate = SSolver.initialize (f s) yinit_nvec in
	SSolver.set_stop_time sstate stop_time;

	(* the zero-crossing solver state *)
	let zstate = ZSolver.initialize_only cstate.zmax (g s) cstate.cvec in

	{ state = s; sstate = sstate; zstate = zstate;
	  yinit_nvec = yinit_nvec; time = 0.0; simu = SimInit } in

      let reset { state; sstate; zstate; yinit_nvec; time = time } =
	reset state;
	SSolver.reinitialize sstate time yinit_nvec;
	ZSolver.reinitialize zstate time cstate.cvec in

      let step
	    ({ state; yinit_nvec; sstate; zstate; simu; time } as s)
	       (horizon, i) =
	try
	(* store the current input *)
	  input := Some(i);
	  (* make a step *)
	  match simu with
	  | SimIntegration | SimDiscrete(Success) ->
             (* make one step of integration *)
             let achieved_time = SSolver.step sstate time yinit_nvec in
             print_string "time = "; print_float time;
	     print_newline ();
	     print_string "achieved time = "; print_float achieved_time;
	     print_newline ();
	     (* is there a zero-crossing? *)
	     cstate.cvec <- SSolver.unvec yinit_nvec;
	     ZSolver.step zstate achieved_time cstate.cvec;
	     let achieved_time, result =
	       if ZSolver.has_roots zstate then
		 let achieved_time =
		   ZSolver.find zstate
				(SSolver.get_dky sstate yinit_nvec, cstate.cvec)
				cstate.zinvec in
		 (* one more step to actualize left limits *)
		 (* and the zero-crossing state variables *)
		 minorstep state achieved_time;
		 achieved_time, RootsFound
	       else
		 if achieved_time >= stop_time
		 then stop_time, StopTimeReached
		 else if achieved_time = s.time
		 then achieved_time, Horizon
		 else achieved_time, Success in
	     s.time <- time;
	     s.simu <- SimDiscrete(result);
	     stop_time, result
	  | SimDiscrete(RootsFound | Horizon) -> 
             (* make a discrete step *)
	     let result = majorstep state time (SSolver.unvec yinit_nvec) i in
	     (* sets all the entries in zinvec to zero *)
             Zls.zzero cstate.zinvec cstate.zmax;
             let result = Cascade(result) in
	     s.simu <- SimDiscrete(result);
             time, result
	  | SimInit | SimDiscrete(Cascade _) ->
             (* a cascade occur, i.e., an event is triggered in zero-time *)
             let result = majorstep state time (SSolver.unvec yinit_nvec) i in
             print_string "time = "; print_float time;
	     print_newline ();
	     print_string "horizon = "; print_float cstate.horizon;
	     print_newline ();
	     if cstate.horizon = 0.0 then
               let result = Cascade(result) in
		s.simu <- SimDiscrete(result);
		time, result
             else
               if s.time >= stop_time
	       then
		 begin
		   s.simu <- SimDiscrete(StopTimeReached);
		   s.time, StopTimeReached
		 end
	       else
		 begin
		   SSolver.reinitialize sstate time yinit_nvec;
		   ZSolver.reinitialize zstate time cstate.cvec;
		   let time =
		     max (s.time +. min horizon cstate.horizon) stop_time in
		   s.time <- time;
		   s.simu <- SimIntegration;
		   s.time, Success
		 end
	  | SimDiscrete(r) -> time, r
	with
	| x -> raise x (* time, Error *) in

      Node { alloc = alloc; step = step; reset = reset }
  end

module Solver = Make (Sundials_cvode) (Illinois)

let solve = Solver.solve
	     
