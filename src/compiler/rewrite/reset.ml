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

(* distribute resets. Applies to normalized equations *)

open Misc
open Location
open Ident
open Zelus
open Mapfold

type acc = { res_list: Typinfo.exp list; stateful: bool }

let empty = { res_list = []; stateful = false }

(* [reset [r1;...;rn] eq = reset [r2;...;rn] (reset eq every r1) *)
let rec reset res_list eq =
  match res_list with
  | [] -> eq | r :: res_list -> reset res_list (Aux.eq_reset eq r)

let equation funs ({ res_list; stateful } as acc) ({ eq_desc } as eq) =
  match eq_desc with
  | EQinit(x, e) ->
     let e, _ = Mapfold.expression_it funs empty e in
     let eq = { eq with eq_desc = EQinit(x, e) } in
     reset res_list eq, { acc with stateful = true }
  | EQeq(p, e) ->
     let e, { stateful = stateful_e } = Mapfold.expression_it funs empty e in
     if stateful_e then reset res_list eq, { acc with stateful = true }
     else eq, acc
  | EQand({ eq_list } as a) ->
     let eq_list, acc = Util.mapfold (equation_it funs) acc eq_list in
     { eq with eq_desc = EQand { a with eq_list } }, acc
  | EQreset(eq, e_r) ->
     Mapfold.equation_it funs { res_list = e_r :: res_list; stateful } eq 
  | _ ->
     let eq, { stateful = stateful_e } = Mapfold.equation funs empty eq in
     if stateful_e then reset res_list eq, { acc with stateful = true }
     else eq, acc
  
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

