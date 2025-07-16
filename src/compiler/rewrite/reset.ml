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
(* for the moment; no distribution. rewrite [reset eq every e] in [eq] *)
(* when [eq] is combinational *)

open Misc
open Location
open Ident
open Zelus
open Mapfold

type acc =
  { res_list: Typinfo.exp list;
    stateful: bool }

let empty = { res_list = []; stateful = false }

(*

(* [reset [r1;...;rn] eq = reset [r2;...;rn] (reset eq every r1) *)
let rec reset res_list eq =
  match res_list with
  | [] -> eq | r :: res_list -> reset res_list (Aux.eq_reset eq r)

(* [res_list = [r1;...;rn]]; [stateful] is a boolean *)
(* [equation funs acc eq = eq', acc'] such that [eq'] is *)
(* the expression [eq] where [res_list] is distributed in all sub-equations *)
(* if [acc = false] and [acc'.stateful = true] then [eq] is stateful *)
(* [r1;...;rn] a list of reset condition. All stateful equations in [eq] *)
(* will be surrended by a reset condition on [r1;...;rn] *)
let equation funs ({ res_list; stateful } as acc) ({ eq_desc } as eq) =
  match eq_desc with
  | EQinit(x, e) ->
     let e, _ = Mapfold.expression_it funs empty e in
     let eq = { eq with eq_desc = EQinit(x, e) } in
     reset res_list eq, { acc with stateful = true }
  | EQeq(p, e) ->
     let e, { stateful = stateful_e } = Mapfold.expression_it funs empty e in
     let eq = { eq with eq_desc = EQeq(p, e) } in
     if stateful_e then reset res_list eq, { acc with stateful = true }
     else eq, acc
  | EQand({ eq_list } as a) ->
     let eq_list, acc = Util.mapfold (Mapfold.equation_it funs) acc eq_list in
     { eq with eq_desc = EQand { a with eq_list } }, acc
  | EQreset(eq, e_r) ->
     let eq, { stateful } =
       Mapfold.equation_it funs { res_list = e_r :: res_list; stateful } eq in
     eq, { acc with stateful }
  | _ ->
     let eq, { stateful = stateful_e } = Mapfold.equation funs empty eq in
     if stateful_e then reset res_list eq, { acc with stateful = true }
     else eq, acc

let expression funs acc e =
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eapp { f; arg_list } ->
     let ty = Typinfo.get_type f.e_info in
     if Types.is_combinatorial (List.length arg_list) ty then e, acc
     else e, { acc with stateful = true }
  | _ -> e, acc
 *)

let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQinit(x, e) ->
     let e, _ = Mapfold.expression_it funs acc e in
     let eq = { eq with eq_desc = EQinit(x, e) } in
     eq, { acc with stateful = true }
  | EQeq(p, e) ->
     let e, acc = Mapfold.expression_it funs acc e in
     let eq = { eq with eq_desc = EQeq(p, e) } in
     eq, acc
  | EQreset(eq_r, e) ->
     (* [reset eq every e] = [eq] if [eq] is combinational *)
     let eq_r, { stateful } = Mapfold.equation_it funs empty eq_r in
     let e, acc = Mapfold.expression_it funs acc e in
     let eq =
       if stateful then { eq with eq_desc = EQreset(eq_r, e) } else eq_r in
     eq, { acc with stateful = acc.stateful || stateful }
  | _ ->  Mapfold.equation funs acc eq

let expression funs acc e =
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eapp { f; arg_list } ->
     let ty = Typinfo.get_type f.e_info in
     if Types.is_combinatorial (List.length arg_list) ty then e, acc
     else e, { acc with stateful = true }
  | _ -> e, acc

(* a function is combinatorial *)
let funexp funs acc f =
  let f, _ = Mapfold.funexp funs empty f in
  f, acc

let sizefun funs acc f =
  let f, _ = Mapfold.sizefun funs empty f in
  f, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with
      funexp; sizefun; expression; equation;
      set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

