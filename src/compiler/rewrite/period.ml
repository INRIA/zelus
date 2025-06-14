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

(* elimation of periods. period(e1|e2) is only allowed in hybrid nodes *)

(* After this step, every hybrid node is supposed to have an implicit state variable *)
(* major_name of kind Major. The lower level code generation step will set it *)

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

(* The translation function for periods *)
let period_t major time phase period =
  (* [local h, z *)
  (*  do init h = time + phase
      and h = horizon (if z then last h + period else last h) *)
  (*  and z = major && (time >= last h) in z] *)
  let h = Ident.fresh "h" in
  let z = Ident.fresh "z" in
  Aux.e_local_vardec [Aux.id_vardec h; Aux.id_vardec z]
    [Aux.par
       [Aux.eq_init h (Aux.plus (Aux.var time) phase);
        Aux.id_eq h (Aux.horizon
                       (Aux.ifthenelse (Aux.var z)
                          (Aux.plus (Aux.last_star h) period)
                          (Aux.last_star h)));
        Aux.id_eq z (Aux.and_op major
                       (Aux.greater_or_equal (Aux.var time)
                          (Aux.last_star z)))]]
    (Aux.var z)

(* Ensure that a zero-crossing cannot be done *)
(* twice without time passing *)
    (*
      let up major time e =
  let z = Zident.fresh "z" in
  let ztime = Zident.fresh "ztime" in
  let env =
    Env.add ztime (Deftypes.entry imemory Initial.typ_float)
	    (Env.add z (Deftypes.entry Sval Initial.typ_float)
		     Env.empty) in
  let eq_list =
    [eq_init ztime minus_one;
     eq_make ztime
	     (ifthenelse (float_var z) (float_var time) (float_last ztime));
     eq_make z
	     (Zaux.up (ifthenelse (greater (float_var time) (float_last ztime))
				e one))] in
  make_let env eq_list (float_var z)
     *)

let get acc = match acc with | None -> assert false | Some(major, time) -> major, time

(* Add the extra input parameter "time" for hybrid nodes *)
let funexp funs acc ({ f_kind; f_env } as f) =
  match f_kind with 
  (* a hybrid node have an implicit state variable of kind "Major" *)
  | Knode(Kcont) -> 
     let major, f_env = Aux.major f_env in 
     let time = fresh () in
     let { f_args; f_env } as f, _ = Mapfold.funexp funs (Some(major, time)) f in
     let head, tail = Util.firsts f_args in
     let f_args =
       head @ [Aux.vardec time false None None :: tail] in
     { f with f_args; f_env = Env.add time Typinfo.no_ienv f_env }, acc
  | _ -> Mapfold.funexp funs acc f

(* add the extra time argument for the application of hybrid nodes *)
let expression funs acc e =
  let { e_desc; e_info } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eapp({ f; arg_list } as app) ->
     (* The type of [f] must be known *)
     let ty_f = Typinfo.get_type f.e_info in
      let arg_list =
       if Types.is_hybrid_funtype (List.length arg_list) ty_f then
         let _, time = get acc in
         let head, tail = Util.firsts arg_list in
         let tail = match tail.e_desc with 
           | Etuple(l) -> { e with e_desc = Etuple (Aux.var time :: l) }
           | _ -> Aux.pair (Aux.var time) tail in
         head @ [tail]
       else arg_list in
     { e with e_desc = Eapp { app with arg_list } }, acc
  | Eop(Eperiod, [phase; period]) -> 
     let major, time = get acc in
     let e = period_t major time phase period in
     e, acc
  | _ -> e, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; funexp; set_index; get_index;
                            global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs None p in
  { p with p_impl_list = p_impl_list }
