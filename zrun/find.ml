(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Ident
open Monad.Opt
open Value
   
(* access function to the symbol table *)
let find_value_opt x env =
  let* { cur } = Env.find_opt x env in
  return cur

let find_last_opt x env =
  let* { last } = Env.find_opt x env in
  last
           
let find_gvalue_opt x env =
  try
    let { Global.info } = Genv.find x env in
    return info
  with
  | Not_found -> none
