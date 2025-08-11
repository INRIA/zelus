(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Elimation of disc. disc(e) is only allowed in hybrid nodes *)

(* [disc(x)] is translated into *)
(* [local cx init x, z do cx = x and z = major && (x <> last* cx) in z] *)

(* After this step, every hybrid node have an implicit state variable *)
(* major of kind Major. The code generation step will set it *)

open Ident
open Zelus
open Aux

type acc = { major: Ident.t option }

let empty = { major = None }

(* The translation function for [disc(e)] *)
let disc major e =
  (* [local x, cx init infinity, z do *)
  (*  x = e and cx = x and z = major && (x <> last* cx) in z] *)
  let x = Ident.fresh "x" in
  let cx = Ident.fresh "cx" in
  let z = Ident.fresh "z" in
  Aux.local_in_e (Aux.block_make [Aux.vardec x false None None;
                               Aux.vardec cx false
                                 (Some(Aux.infinity)) None;
                               Aux.vardec z false None None]
                 [Aux.eq_and
                    (Aux.id_eq x e)
                    (Aux.eq_and (Aux.id_eq cx (Aux.var x))
                       (Aux.id_eq z (Aux.and_op (Aux.var major)
                                       (Aux.diff (Aux.var x)
                                          (Aux.last_star cx)))))])
    (Aux.var z)

(* get the [major] variable *)
let get { major } =
  let major =
    match major with | None -> Ident.fresh "major" | Some(m) -> m in
  major, { major = Some(major) }

let get_from_hidden_env f_hidden_env =
  { major = Aux.get_hidden_state_variable Major f_hidden_env }

let update_hidden_env { major } f_hidden_env =
  let f_env =
    match major with 
    | None -> Env.empty | Some(m) -> Aux.major_entry m Env.empty in
  Env.append f_env f_hidden_env

(* [acc = None or Some(major)] *)
let expression funs acc e =
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eop(Edisc, [e]) ->
     let major, acc = get acc in
     disc major e, acc
  | _ -> e, acc

let funexp funs acc ({ f_kind; f_hidden_env } as f) =
  match f_kind with 
  (* a hybrid node have an implicit state variable of kind "Major" *)
  | Knode(Kcont) -> 
     let f_acc = get_from_hidden_env f_hidden_env in
     let f, f_acc = Mapfold.funexp funs f_acc f in
     let f_hidden_env = update_hidden_env f_acc f_hidden_env in
     { f with f_hidden_env }, acc
  | _ -> Mapfold.funexp funs acc f

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with funexp; expression; set_index; get_index;
                            global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
