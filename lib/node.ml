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
(* a discrete one. Embeds the numerical solver into the internal state *)

(* compile with:
*- ocamlfind ocamlc bigarray.cma sundials.cma ztypes.ml node2.ml *)
open Ztypes


type 'a return =
      | Success (* the integration has reached the expected horizon *)
      | RootsFound (* a Root has been found during integration *)
      | Cascade of 'a (* a new event occur in zero-time *)
      | StopTimeReached (* the end of simulation time is reached *)
      | Init
      | Error

module Make (SSolver: Zls.STATE_SOLVER) (ZSolver: Zls.ZEROC_SOLVER) =
  struct
    (* the status return by one step of computation *)
    (* the type that define the internal state of the node *)
    type ('a, 's) sstate =
	{ state: 's; (* the discrete state *)
	  zstate: ZSolver.t; (* the solver state *)
	  sstate: SSolver.t; (* the zero-crossing solver state *)
	  yinit_nvec: SSolver.nvec; (* the state vector for the solver *)
	  mutable time: float; (* the current time of the simulation *)
	  mutable result: 'a return; (* the result of the simulation step *)
	}
  
    let take = function | None -> assert false | Some(v) -> v

    (* Lift a hybrid node into a node *)
    (* [solve f stop_time (input, t) = next_t, result]
       - f : 'a -C-> 'b is the hybrid node;
       - stop_time : float is the stop time of the simulation;
       - input : 'a is a stream;
       - t : float is a stream of horizons that must be increasing
             (forall n in Nat. t(n) <= t(n+1))
       - result : 'b return is a stream of results;
       - next_t : float is a stream of achieved horizons *)
    let solve f (stop_time: float) =
      let cstate =
	{ cvec = Zls.cmake 0; dvec = Zls.cmake 0; cindex = 0; zindex = 0;
	  cend = 0; zend = 0; cmax = 0; zmax = 0;
	  zinvec = Zls.zmake 0; zoutvec = Zls.cmake 0;
	  major = false; horizon = 0.0 } in

      let input = ref None in

      (* create a node *)
      let Node { alloc; step; reset } = f cstate in
      
      (* the derivative *)
      let f s time cvec dvec =
	cstate.cvec <- cvec;
	cstate.dvec <- dvec;
	cstate.cindex <- 0;
	cstate.major <- false;
	ignore (step s (time, take !input)) in
  
      (* the zero-crossing function *)
      let g s time cvec zoutvec =
	cstate.cvec <- cvec;
	cstate.zoutvec <- zoutvec;
	cstate.cindex <- 0;
	cstate.major <- false;
	ignore (step s (time, take !input)) in
  
      (* the minorstep function *)
      let minorstep s time =
	cstate.cindex <- 0;
	cstate.major <- false;
	step s (time, take !input) in

      (* the majorstep function *)
      let majorstep s time i =
	cstate.cindex <- 0;
	cstate.major <- true;
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
	  yinit_nvec = yinit_nvec; time = 0.0; result = Init } in

      let reset { state; sstate; zstate; yinit_nvec; time = time } =
	reset state;
	SSolver.reinitialize sstate time yinit_nvec;
	ZSolver.reinitialize zstate time cstate.cvec in

      let step
	    ({ state; yinit_nvec; sstate; zstate; result; time } as s)
	       (horizon, i) =
	try
	  (* store the current input *)
	  input := Some(i);
	  (* make a step *)
	  match result with
	  | Success ->
             print_string "two\n"; flush stdout;
	     (* make one step of integration *)
             let next_time = SSolver.step sstate time yinit_nvec in
             (* is there a zero-crossing? *)
	     ZSolver.step zstate next_time cstate.cvec;
	     let stop_time, result =
	       if ZSolver.has_roots zstate then
		 let stop_time =
		   ZSolver.find zstate
				(SSolver.get_dky sstate yinit_nvec, cstate.cvec)
				cstate.zinvec in
		 (* one more step to actualize left limits *)
		 (* and the zero-crossing state variables *)
		 minorstep state time;
		 stop_time, RootsFound
	       else next_time, Success in
	     s.result <- RootsFound; 
	     s.time <- stop_time;
	     stop_time, result
	  | RootsFound ->
             print_string "three\n"; flush stdout;
	     (* a root has been found. *)
	     (* make a discrete step *)
	     let r = majorstep state time i in
	     print_string "three 2\n"; flush stdout;
	     (* sets all the entries in zinvec to zero *)
             Zls.zzero cstate.zinvec cstate.zmax;
             let r = Cascade(r) in
	     s.result <- r;
             time, r
	  | Init | Cascade _ ->
             print_string "four\n"; flush stdout;
	     (* a cascade occur, i.e., an event is triggered in zero-time *)
             let r = majorstep state time i in
             if cstate.horizon = 0.0 then
               let r = Cascade(r) in
	       s.result <- r;
	       time, r
             else
               begin
		 SSolver.reinitialize sstate time yinit_nvec;
		 ZSolver.reinitialize zstate time cstate.cvec;
		 s.time <- s.time +. cstate.horizon;
		 s.result <- Success;
		 s.time, Success
	       end
	  | StopTimeReached
	  | Error -> print_string "five\n"; flush stdout;
		     time, result
	with
	| x -> print_string "six\n"; flush stdout;
	       raise x; time, Error in

      Node { alloc = alloc; step = step; reset = reset }
  end

module Solver = Make (Sundials_cvode) (Illinois)

let solve = Solver.solve
	     
