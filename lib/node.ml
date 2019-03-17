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

(* This module provides functions to lift a *)
(* hybrid function (with type 'a -C-> 'b) into a node (with type 'a -D-> 'b) *)
(* it builts on Sundials cvode; we may provide a more generic version in the future *)

(* compile with ocamlfind ocamlc bigarray.cma sundials.cma node.ml -package sundialsml *)
open Ztypes
open Bigarray
open Sundials

(* turn error exception raises by cvode (see the Sundials.Cvode module) into a value *)
type error =
  | IllInput
  | TooClose
  | TooMuchWork
  | TooMuchAccuracy
  | ErrFailure
  | ConvergenceFailure
  | LinearInitFailure
  | LinearSetupFailure
  | LinearSolveFailure
  | RhsFuncFailure
  | FirstRhsFuncFailure
  | RepeatedRhsFuncFailure
  | UnrecoverableRhsFuncFailure
  | RootFuncFailure
  
(* the result of a step made by the solver *)
type result =
  | Success (* the integration has reached the expected horizon *)
  | RootsFound (* a Root has been found during integration *)
  | Cascade (* a new event occur in zero-time *)
  | StopTimeReached (* the end of simulation time is reached *)
  | Error of error
           
(* convert the result made by cvode into a result *)
let convert_cvode_result r =
  match r with
  | Cvode.Success -> Success
  | Cvode.RootsFound -> RootsFound
  | Cvode.StopTimeReached -> StopTimeReached

(* allocate the state vector *)
let cmake = Array1.create float64 c_layout
(* allocate the vector of zero-crossings *)
let zmake n =
  let r = Array1.create int32 c_layout n in
  Array1.fill r 0l; r
(* sets the zin vector *)
let zwrap length zinit zinvec =
  for i = 0 to length - 1 do
    if Roots.rising zinit i then zinvec.{i} <- 1l else zinvec.{i} <- 0l
  done

  
(* The interface with the solver *)
type cstate =
  { mutable dvec : dvec; (* the vector of derivatives *)
    mutable cvec : cvec; (* the vector of positions *)
    mutable zinvec : zinvec; (* the vector of boolean; true when the
                             solver has detected a zero-crossing *)
    mutable zoutvec : zoutvec; (* the corresponding vector that define
                               zero-crossings *)
    mutable cstart : int; (* the start position in the vector of positions *)
    mutable zstart : int; (* the start position in the vector of zero-crossings *)
    mutable cend : int; (* the maximum size of the vector of positions *)
    mutable zend : int; (* the maximum number of zero-crossings *)
    mutable horizon : float; (* the next horizon *)
    mutable discrete : bool; (* integration iff [discrete = false] *)
  }

type ('a, 'b) state =
  { state: 'a; 
    yinit: (Nvector_serial.data, Nvector_serial.kind) Nvector.t;
    zinit: Roots.t;
    sstate: 'b }
  
  
(* Lift a hybrid function (type 'a -C-> 'b) into a node ('a -D-> 'b) *)
(* Its Zelus interface is:
 *- val go: ('a -C-> 'b) -S-> horizon -S-> horizon * result * 'a -D-> horizon * result *)
let go f stop_time =
  let cstate =
    { cvec = cmake 0;
      dvec = cmake 0;
      cstart = 0;
      cend = 0;
      zstart = 0;
      zend = 0;
      zinvec = zmake 0;
      zoutvec = cmake 0;
      discrete = false;
      horizon = 0.0 } in

  (* create a node *)
  let Node { alloc; step; reset }, cmax, zmax = f cstate in
  
  (* the derivative *)
  let f s time y yd =
    cstate.cvec <- y;
    cstate.dvec <- yd;
    ignore (step s ()) in
  
  (* the zero-crossing function *)
  let g s time y zyout =
    cstate.cvec <- y;
    cstate.zoutvec <- zyout;
    ignore (step s ()) in
  
  (* the step function *)
  let step = step in
  
  (* the alloc function *)
  let alloc () =
    cstate.cvec <- cmake cstate.cend;
    cstate.dvec <- cmake cstate.cend;
    cstate.zoutvec <- cmake cstate.zend;
    cstate.zinvec <- zmake cstate.zend;
    cstate.horizon <- 0.0;
    cstate.discrete <- true;

    let yinit = Nvector_serial.wrap cstate.cvec in
    
    let zinit = Roots.create cstate.zend in
    
    let state = alloc () in

    (* the solver state *)
    let sstate =
      Cvode.(init Adams Functional
               (SStolerances (1e-4, 1e-8))
               (f state) ~roots:(cstate.zend, (g state)) 0.0 yinit) in

    Cvode.set_stop_time sstate stop_time;
    Cvode.set_all_root_directions sstate RootDirs.Increasing;
    { state = state; yinit = yinit; zinit = zinit; sstate = sstate } in
    
  let step { state; yinit; zinit; sstate } (time, r, x) =
    try
      match r with
      | Success ->
         cstate.discrete <- false;
         let next_t, r = Cvode.solve_normal sstate time yinit in
         next_t, convert_cvode_result r
      | RootsFound ->
         Cvode.get_root_info sstate zinit;
         cstate.cvec <- Nvector_serial.unwrap yinit;
         zwrap cstate.zend zinit cstate.zinvec;
         cstate.discrete <- true;
         ignore (step state ());
         if cstate.horizon = 0.0 then time, Cascade
         else
           (Cvode.reinit sstate time yinit; time, Success)
      | StopTimeReached | Error _ -> time, r
    with
    | Cvode.IllInput -> time, Error IllInput 
    | Cvode.TooClose -> time, Error TooClose
    | Cvode.TooMuchWork -> time, Error TooMuchWork
    | Cvode.TooMuchAccuracy -> time, Error TooMuchAccuracy
    | Cvode.ErrFailure -> time, Error ErrFailure
    | Cvode.ConvergenceFailure -> time, Error ConvergenceFailure
    | Cvode.LinearInitFailure -> time, Error LinearInitFailure
    | Cvode.LinearSetupFailure -> time, Error LinearSetupFailure
    | Cvode.LinearSolveFailure -> time, Error LinearSolveFailure
    | Cvode.RhsFuncFailure -> time, Error RhsFuncFailure
    | Cvode.FirstRhsFuncFailure -> time, Error FirstRhsFuncFailure
    | Cvode.RepeatedRhsFuncFailure -> time, Error RepeatedRhsFuncFailure
    | Cvode.UnrecoverableRhsFuncFailure -> time, Error UnrecoverableRhsFuncFailure
    | Cvode.RootFuncFailure -> time, Error RootFuncFailure in
  
  let reset { state; yinit; sstate } =
    reset state;
    Cvode.reinit sstate 0.0 yinit in

  Node { alloc = alloc; step = step; reset = reset }
    
