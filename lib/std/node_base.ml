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
  if !debug then
    begin print_string s; print_float i; print_newline (); flush stdout end

type status =
  | Interpolate (* no integration was necessary *)
  | Success of float (* the integration succeed; limit time for correctness *)
  | RootsFound (* a root has been found *)
  | Horizon of float (* returns the next horizon (time event) *)
  | Cascade (* a cascade *)
  | StopTimeReached (* the end of simulation time is reached *)
  | TimeHasPassed (* an output at time [h] is expected but *)
  (* [h < start] where [start] *)
  (* is the last restart time of the solver *)
  | Error (* something went wrong during integration *)

(* output *)
type 'b return = { time: float; status: status; result: 'b }


module Make (SSolver: Zls.STATE_SOLVER) (ZSolver: Zls.ZEROC_SOLVER) =
struct
  (* the state of the solver. Either never called (allocated) or running *)
  type ('a, 'b) solver =
    | Init (* initial state of the simulation *)
    | Running of ('a, 'b) solver_state

  and ('a, 'b) solver_state =
    { zstate: ZSolver.t;
      (* the solver state *)
      sstate: SSolver.t;
      (* the zero-crossing solver state *)
      roots: Ztypes.zinvec;
      (* the vector of zero-crossing *)
      nvec: SSolver.nvec;
      (* the vector of positions *)
      cvec: Ztypes.cvec;
      (* in two forms *)
      mutable t_start: float;
      (* time of the previous reset or mesh point *)
      mutable t_limit: float;
      (* time for the limit of the next solver step, i.e., next time event *)
      mutable t_mesh: float;
      (* horizon reached by the solver. *)
      (* No zero-crossing in [t_start, t_mesh] *)
      mutable t_time: float;
      (* current time *)
      minput: 'a ref; (* the input is read at discrete-time instants *)
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
    (* convert the internal representation of a hybrid node *)
    (* into one that can be used by an ODE/Zero-crossing solver *)
    let Hnode
        { state; zsize; csize; derivative; crossing;
          output; setroots; majorstep; reset; horizon } = Lift.lift f in

    (* the allocation function *)
    let alloc () =
      (* At this point, we do not allocate the solver states yet. *)
      (* this is due to the way we compile which expect the derivative *)
      (* and zero-crossing function to expect an input *)
      (* We will change this once those two functions are obtained *)
      (* through slicing and will not need an input *)
      { state = state; solver = Init } in

    let reset { state; solver } =
      reset state;
      match solver with
      | Init -> ()
      | Running ({ nvec; cvec; zstate; sstate; t_time } as s) ->
        (* reset the ODE solver and Zero-crossing solver *)
        let _ = SSolver.get_dky sstate nvec 0.0 0 in
        SSolver.reinitialize sstate 0.0 nvec;
        ZSolver.reinitialize zstate 0.0 cvec;
        s.t_start <- 0.0;
        s.t_time <- 0.0;
        s.t_mesh <- 0.0 in

    (* the step function *)
    let step ({ state; solver } as s) (expected_time, input) =
      try
        (* make a step *)
        match solver with
        | Init ->
          (* allocate the vectors for continuous state variables *)
          (* and that for the zero-crossing detection *)
          let nvec = SSolver.cmake csize in
          let cvec = SSolver.unvec nvec in
          let roots = Zls.zmake zsize in

          log_info "Init: start = " 0.0;
          (* initial major step *)
          let result = majorstep state 0.0 cvec input in

          let minput = ref input in

          let derivative time cvec dvec =
            derivative state !minput time cvec dvec in

          let crossing time cvec dvec =
            crossing state !minput time cvec dvec in

          (* Allocate the solver *)
          let sstate =
            SSolver.initialize derivative nvec in
          (* Allocate the zsolver *)
          let zstate =
            ZSolver.initialize zsize crossing cvec in
          SSolver.set_stop_time sstate stop_time;

          let horizon = horizon state in
          let t_limit = min stop_time horizon in
          let next, status =
            if horizon = 0.0 then Discrete(false), Cascade
            else
            if stop_time <= 0.0 then End, StopTimeReached
            else Integrate, Horizon(t_limit) in
          s.solver <- Running { sstate = sstate; zstate = zstate;
                                t_start = 0.0; t_limit = t_limit;
                                t_mesh = 0.0; t_time = 0.0;
                                minput = minput; output = result;
                                roots = roots; cvec = cvec; nvec = nvec;
                                next = next };
          log_info "horizon = " t_limit;
          { time = 0.0; status = status; result = result }
        | Running({ next; sstate; zstate; t_start; t_mesh; t_limit;
                    t_time; minput; nvec; cvec; roots } as s) ->
          log_info "Expected time = " expected_time;
          if expected_time < t_start then
            { time = t_start; status = TimeHasPassed; result = s.output }
          else
            (* if the input did not change since the last reset *)
            (* of the solvers and expected_time is less than t_mesh *)
            (* interpolate the state at the expected_time *)
            let input_change =
              (expected_time > t_time) && not (!minput = input) in
            s.t_time <- expected_time;
            if expected_time <= t_mesh then
              if not input_change then
                (* interpolation *)
                let _ = SSolver.get_dky sstate nvec expected_time 0 in
                let result = output state input cvec in
                s.output <- result;
                log_info "Interpolate: time = " expected_time;
                { time = expected_time; status = Interpolate;
                  result = result }
              else (* if the input has changed since the last step *)
                (* the solution estimated by the solver is wrong and *)
                (* must be cancelled *)
                let _ = SSolver.get_dky sstate nvec t_time 0 in
                log_info "Change of the input at t_time = " t_time;
                let result = majorstep state t_time cvec input in
                s.t_start <- t_time;
                s.t_mesh <- t_time;
                s.minput := input;
                s.output <- result;
                let status =
                  let horizon = horizon state in
                  if horizon = 0.0
                  then begin s.next <- Discrete(false); Cascade end
                  else
                    let _ = SSolver.reinitialize sstate t_mesh nvec in
                    let _ = ZSolver.reinitialize zstate t_mesh cvec in
                    let t_limit = min stop_time horizon in
                    s.t_start <- t_mesh;
                    s.t_limit <- t_limit;
                    s.next <- Integrate;
                    Horizon(t_limit) in
                { time = t_mesh; status = status; result = s.output }
            else
              match next with
              | Integrate ->
                log_info "Integrate: t_mesh = " t_mesh;
                (* the new start point [t_start] is now [t_mesh] *)
                s.t_start <- t_mesh;
                if t_mesh >= stop_time then
                  begin
                    s.next <- End;
                    s.t_time <- expected_time;
                    { time = stop_time; status = StopTimeReached;
                      result = s.output }
                  end
                else
                  let t_limit_with_margin = add_margin t_limit in
                  log_info "t_limit_with_margin = " t_limit_with_margin;
                  let t_nextmesh =
                    (* integrate *)
                    SSolver.step sstate t_limit_with_margin nvec in
                  (* interpolate if the mesh point has passed the *)
                  (* time limit *)
                  log_info "t_nextmesh = " t_nextmesh;
                  let t =
                    if t_limit < t_nextmesh
                    then
                      (SSolver.get_dky sstate nvec t_limit 0; t_limit)
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
                      log_info "root found at time = " t;
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
                  s.t_time <- expected_time;
                  { time = s.t_start; status = status; result = s.output }
              | Discrete(is_zero_crossing) ->
                log_info "StepRootsFound or StepCascade: time = " t_mesh;
                if is_zero_crossing
                then setroots state input cvec roots;
                let result = majorstep state t_mesh cvec input in
                s.output <- result;
                let status =
                  let horizon = horizon state in
                  if horizon = 0.0
                  then begin s.next <- Discrete(false); Cascade end
                  else
                    let _ = SSolver.reinitialize sstate t_mesh nvec in
                    let _ = ZSolver.reinitialize zstate t_mesh cvec in
                    let t_limit = min stop_time horizon in
                    s.t_start <- t_mesh;
                    s.t_limit <- t_limit;
                    s.next <- Integrate;
                    Horizon(t_limit) in
                { time = t_mesh; status = status; result = s.output }
              | End ->
                log_info "End: stop_time = " stop_time;
                { time = s.t_start; status = StopTimeReached;
                  result = s.output }
      with
      | x -> raise x in
    Node { alloc = alloc; step = step; reset = reset }
end

module Ode23Solver = Make (Solvers.Ode23) (Illinois)
module Ode45Solver = Make (Solvers.Ode45) (Illinois)
(* module SundialsSolver = Make (Solvers.Sundials_cvode) (Illinois) *)

let solve_ode23 = Ode23Solver.solve
let solve_ode45 = Ode45Solver.solve
(* let solve = SundialsSolver.solve *)
