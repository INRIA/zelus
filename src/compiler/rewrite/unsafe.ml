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

(* safe/unsafe expressions and equations. *)
(* A computation is safe when it is combinatorial, that is, it *)
(* has no side effect, total and no state *)
open Zelus
open Ident
open Deftypes
open Aux
       
(* An expression or equation is unsafe if it contains an unsafe operation. *)
let expression funs acc e =
  let { e_desc; e_info } as e, acc = Mapfold.expression funs acc e in
  if acc then e, acc
  else
    let ty = Typinfo.get_type e_info in
    match e_desc with
    | Eapp { f; arg_list } ->
       (* look if (f e1...en) is combinatorial *)
       e, (not (Types.is_combinatorial (List.length arg_list) ty))
    | _ -> e, acc

let expression e =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; global_funs } in
  let _, acc = Mapfold.expression_it funs false e in
  acc

