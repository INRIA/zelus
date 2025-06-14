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

(* Elimation of disc. disc(e) is only allowed in hybrid nodes *)

(* [disc(x)] is translated into *)
(* [local cx init x, z do cx = x and z = major && (x <> last* cx) in z] *)

(* After this step, every hybrid node is supposed to have an implicit state variable *)
(* major of kind Major. The lower level code generation step will set it *)

open Ident
open Zelus
open Aux

(* The translation function for [disc(e)] *)
let disc major e =
  (* [local x, cx init infinity, z do *)
  (*  x = e and cx = x and z = major && (x <> last* cx) in z] *)
  let x = Ident.fresh "x" in
  let cx = Ident.fresh "cx" in
  let z = Ident.fresh "z" in
  Aux.e_local (Aux.block_make [Aux.vardec x false None None;
                               Aux.vardec cx false
                                 (Some(Aux.infinity)) None;
                               Aux.vardec z false None None]
                 [Aux.eq_and
                    (Aux.id_eq x e)
                    (Aux.eq_and (Aux.id_eq cx (Aux.var x))
                       (Aux.id_eq z (Aux.and_op major
                                       (Aux.diff (Aux.var x)
                                          (Aux.last_star cx)))))])
    (Aux.var z)

(* [acc = None or Some(major)] *)
let expression funs acc e =
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eop(Edisc, [e]) ->
     let e = match acc with 
       | None -> assert false | Some(major) -> disc major e in
     e, acc
  | _ -> e, acc

let funexp funs acc ({ f_kind; f_env } as f) =
  let acc, f_env = 
    match f_kind with 
    (* a hybrid node have an implicit state variable of kind "Major" *)
    | Knode(Kcont) -> 
       let major, f_env = Aux.major f_env in Some(major), f_env
    | _ -> None, f_env in
  Mapfold.funexp funs acc f

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with funexp; expression; set_index; get_index;
                            global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs None p in
  { p with p_impl_list = p_impl_list }
