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

(* Rewrites [returns (p) eq] into [let eq in p] *)

open Zelus

let exp_of_block { b_vars } =
  let vardec { var_name } = Aux.var var_name in
  let v_list = List.map vardec b_vars in
  match v_list with
  | [] -> assert false
  | [v] -> v
  | _ -> Aux.tuple v_list

let result funs acc r =
  let { r_desc; r_info; r_loc } as r, acc = Mapfold.result funs acc r in
  let r_desc, acc = match r_desc with
    | Exp _ -> r_desc, acc
    | Returns(b_eq) ->
       let e = { e_desc = Elocal(b_eq, exp_of_block b_eq); e_info = r_info;
                 e_loc = r_loc } in
       Exp(e), acc in
  { r with r_desc }, acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with result; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs () p in
  { p with p_impl_list = p_impl_list }
