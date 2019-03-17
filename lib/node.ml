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

(* Error exception raised by cvode (see the Sundials.Cvode module) *)
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
type solver_status =
  | Success (* the integration has reached the expected horizon *)
  | RootsFound (* a Root has been found during integration *)
  | Cascade (* a new event occur in zero-time *)
  | StopTimeReached (* the end of simulation time is reached *)
  | Error of error
           
(* convert the result made by cvode into a result *)
let convert_cvode_status r =
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
(* fill zinvec with zeros *)
let zzero length zinit zinvec =
  for i = 0 to length - 1 do
    zinvec.{i} <- 0l
  done

  
type ('a, 'b) state =
  { state: 'a; 
    yinit: (Nvector_serial.data, Nvector_serial.kind) Nvector.t;
    zinit: Roots.t;
    sstate: 'b }
  
type ('a, 'b) s = { s: 'a; mutable x: 'b }

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
  let Node { alloc; step; reset } = f cstate in
  
  (* the derivative *)
  let f { s; x } time y yd =
    cstate.cvec <- y;
    cstate.dvec <- yd;
    ignore (step s x) in
  
  (* the zero-crossing function *)
  let g { s; x } time y zyout =
    cstate.cvec <- y;
    cstate.zoutvec <- zyout;
    ignore (step s x) in
  
  (* the step function *)
  let step ({ s; x } as sx) input =
    sx.x <- input; step s input in
  
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
    
    let state = { s = alloc (); x = () } in

    (* the solver state *)
    let sstate =
      Cvode.init Cvode.Adams Cvode.Functional
               (Cvode.SStolerances (1e-4, 1e-8))
               (f state) ~roots:(cstate.zend, (g state)) 0.0 yinit in

    Cvode.set_stop_time sstate stop_time;
    Cvode.set_all_root_directions sstate RootDirs.Increasing;
    { state = state; yinit = yinit; zinit = zinit; sstate = sstate } in

  let reset { s } = reset s in
  
  let step { state; yinit; zinit; sstate } (time, status, input) =
    try
      match status with
      | Success ->
         (* make one step of integration *)
         cstate.discrete <- false;
         let next_t, status = Cvode.solve_normal sstate time yinit in
         next_t, None, convert_cvode_status status
      | RootsFound ->
         (* a root has been found; set the zinvec and make a step *)
         Cvode.get_root_info sstate zinit;
         cstate.cvec <- Nvector_serial.unwrap yinit;
         zwrap cstate.zend zinit cstate.zinvec;
         cstate.discrete <- true;
         let result = step state input in
         (* sets the all entries in zinvec to zero *)
         zzero cstate.zend zinit cstate.zinvec;
         time, Some(result), Cascade
      | Cascade ->
         (* a cascade occur, that is, a event is triggered without time passing *)
         cstate.discrete <- true;
         let result = step state input in
         if cstate.horizon = 0.0 then time, Some(result), Cascade
         else (Cvode.reinit sstate time yinit; time, Some(result), Success)
      | StopTimeReached | Error _ -> time, None, status
    with
    | Cvode.IllInput -> time, None, Error IllInput 
    | Cvode.TooClose -> time, None, Error TooClose
    | Cvode.TooMuchWork -> time, None, Error TooMuchWork
    | Cvode.TooMuchAccuracy -> time, None, Error TooMuchAccuracy
    | Cvode.ErrFailure -> time, None, Error ErrFailure
    | Cvode.ConvergenceFailure -> time, None, Error ConvergenceFailure
    | Cvode.LinearInitFailure -> time, None, Error LinearInitFailure
    | Cvode.LinearSetupFailure -> time, None, Error LinearSetupFailure
    | Cvode.LinearSolveFailure -> time, None, Error LinearSolveFailure
    | Cvode.RhsFuncFailure -> time, None, Error RhsFuncFailure
    | Cvode.FirstRhsFuncFailure -> time, None, Error FirstRhsFuncFailure
    | Cvode.RepeatedRhsFuncFailure -> time, None, Error RepeatedRhsFuncFailure
    | Cvode.UnrecoverableRhsFuncFailure -> time, None, Error UnrecoverableRhsFuncFailure
    | Cvode.RootFuncFailure -> time, None, Error RootFuncFailure in
  
  let reset { state; yinit; sstate } =
    reset state;
    Cvode.reinit sstate 0.0 yinit in

  Node { alloc = alloc; step = step; reset = reset }
    
