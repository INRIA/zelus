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
open Lident
open Zelus
       
(* the safe/unsafe sort must be added to the sorting mechanism during typing *)
(* for the moment, we restrict safe functions to be the following ones *)
let list_of_primitives =
  ["+", 2;
   "-", 2;
   "~-", 1;
   "-", 2;
   "/", 2;
   "*", 2;
   "+.", 2;
   "-.", 2;
   "~-.", 1;
   "-.", 2;
   "/.", 2;
   "*.", 2;
   "sqrt", 1;
   "sin", 1;
   "cos", 1;
   "abs_float", 1;
   "abs", 1;
   "not", 1;
   "&&", 2;
   "&", 2;
   "or", 2;
   "||", 2;
   "mod", 2;
   "=", 2;
   "<", 2;
   ">", 2;
   "<=", 2;
   ">=", 2]

module Env = Map.Make(String)

let env_of_primitives =
  List.fold_left (fun acc (p, arity) -> Env.add p arity acc) Env.empty 
    list_of_primitives

(* An expression or equation is unsafe if it contains an unsafe operation. *)
let rec expression { e_desc } =
  match e_desc with
  | Econst _ | Econstr0 _ -> true
  | Econstr1 { arg_list } | Etuple(arg_list) ->
     List.for_all expression arg_list
  | Eapp { f = { e_desc = Eglobal { lname = Modname { qual; id } } };
           arg_list } ->
     if qual = Misc.name_of_stdlib_module 
     then try
         let arity = Env.find id env_of_primitives in
         (arity = List.length arg_list) && (List.for_all expression arg_list)
       with
         Not_found -> false
     else false
  | _ -> false
