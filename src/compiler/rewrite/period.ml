(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* elimation of periods. *)

(* For every function, an extra input [time] is added. A period (v1|v2) *)
(* is translated into the computation of an horizon *)

(* [period(v1(v2))] is translated into *)
(* [local [horizon] h, z *)
(*  do  init h = time + v1 *)
(*  and h = if z then last h + v2 else last h + (time - last time) *)
(*  and z = major && (time >= last h) in *)
(*  z *)

(* [timer(v)] is translated into *)
(* [local [horizon] h, z *)
(*  do init h = time + v *)
(*  and h = if z then infinity else last h + (time - last time) *)
(*  and z = major && (time >= last h) *)
(*  in z] *)

(* An other possible interpretation is to consider that periods and timers *)
(* and taken on absolute time. This is not what is implemented currently. *)
(* The implementation would be: *)

(* [period(v1(v2))] is translated into: *)
(* [local [horizon] h, cpt, z *)
(*  do cpt = 0 -> if z then pre cpt + 1 else pre cpt *)
(*  and h = cpt * v2 + v1 and z = major && (mod_float time v2 = v1) *)
(*  in z] *)

(* [timer(v)] is translated into: *)
(* [local [horizon] h, z *)
(*  do init h = v and h = if z then infinity else last h *)
(*  and z = major && (time = v) in z] *)

(* finally, it is possible to consider that timers and period are taken on *)
(* absolute time but with a starting date which is local. *)

(* [period(v1(v2))] is translated into: *)
(* local [horizon] h *)
(* do init h = time and z = major && (mod_float (time - last h) v2 = v1) *)
(* and h = if z then time + v2 else last h in z *)

(* A zero-crossing cannot be true twice without time passing *)
(* up(x) =>
    let rec init ztime = -1.0
        and ztime = if z then time else last ztime
        and z = up(if time > last ztime then x else 1.0) in
    z *)

open Ident
open Zelus
open Mapfold

let fresh () = Ident.fresh "time"

type acc = { time: Ident.t option }

let empty = { time = None }

let intro { time } =
  let t = match time with | None -> fresh () | Some(t) -> t in
  t, { time = Some t }

(* The translation function for periods *)
let period major time phase period =
  (* [local h init time + phase, z *)
  (*  do h = horizon (if z then last h + period else last h) *)
  (*  and z = major && (time >= last h) in z] *)
  let h = Ident.fresh "h" in
  let z = Ident.fresh "z" in
  Aux.e_local (Aux.block_make [Aux.vardec h false
                                 (Some(Aux.plus (Aux.var time) phase)) None;
                               Aux.vardec z false None None]
                 [Aux.eq_and
                    (Aux.id_eq h (Aux.horizon
                                    (Aux.ifthenelse (Aux.var z)
                                        (Aux.plus (Aux.last_star h) period)
                                        (Aux.last_star h))))
                       (Aux.id_eq z (Aux.and_op major
                                       (Aux.greater_or_equal (Aux.var time)
                                          (Aux.last_star z))))])
    (Aux.var z)

(* Add the extra input parameter "time" for hybrid nodes *)
let funexp funs acc ({ f_kind } as f) =
  match f_kind with
  | Knode(Kcont) ->
     let { f_args; f_env } as f, acc_local = Mapfold.funexp funs empty f in
     let time, _ = intro acc_local in
     { f with f_args = [Aux.vardec time false None None] :: f_args;
              f_env = Env.add time Typinfo.no_ienv f_env }, acc
  | _ -> raise Mapfold.Fallback

(* add the extra time argument for the application of hybrid nodes *)
let expression funs acc ({ e_desc } as e) =
  match e_desc with
  | Eapp({ f; arg_list } as app) ->
     (* we need to know if [f] is hybrid or not *)
     (* for the moment, we suppose it is; this means that this rewriting *)
     (* step must be done after type inference *)
     let f, acc = Mapfold.expression_it funs acc f in
     let arg_list, acc =
       Util.mapfold (Mapfold.expression_it funs) acc arg_list in
     let t, acc = intro acc in
     { e with e_desc = Eapp({ app with f; arg_list = (Aux.var t) :: arg_list }) },
     acc
  | _ -> raise Mapfold.Fallback

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; funexp; set_index; get_index;
                            global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
