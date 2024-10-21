(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2023 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* computes the set of module identifiers used by the current module *)

open Lident
open Mapfold

module StringSet = Set.Make(struct type t = string let compare = compare end)

let add acc lname =
  match lname with
  | Name _ -> acc
  | Modname { qual } ->
     if StringSet.mem qual acc then acc else StringSet.add qual acc

let lident global_funs = add
let typeconstr global_funs = add
let open_t global_funs = add
                      
let program _ p =
  let global_funs =
    { Mapfold.default_global_funs with lident; typeconstr; open_t } in
  let funs =
    { Mapfold.defaults with global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
