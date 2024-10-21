(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Evaluation of combinatorial expressions. The input environment *)
(* is only made of primitive values *)
(* The presence of a stateful construct leads to an error *)
open Misc
open Error
open Monad
open Result
open Ident
open Find
open Ast
open Value
open Primitives
open Match
open Debug


(* merge two environments provided they do not overlap *)
let merge loc env1 env2 =
  let s = Env.to_seq env1 in
  seqfold
    (fun acc (x, entry) ->
      if Env.mem x env2 then error { kind = Emerge_env; loc = loc }
      else return (Env.add x entry acc))
    env2 s


(* check assertion *)
let check_assertion loc ve ret =
  (* when ve is not bot/nil it must be true *)
  match ve with
  | Vnil | Vbot -> return ret
  | Value(v) ->
     let* v = is_bool v |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
     (* stop when [no_assert = true] *)
     if !no_assert || v then return ret
     else error { kind = Eassert_failure; loc = loc }

(* [let+ x = e in e'] returns [bot] if [e] returns bot; *)
(* nil if e returns nil; [e'] otherwise *)
let (let+) v f =
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) -> f v

let (and+) v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(v1, v2)

(* [let*+ x = e in e'] composes [let*] and [let+] *)
let (let*+) v f =
  let* v = v in
  let+ v = v in
  f v

(* check that a value is an integer *)
let is_int loc v =
  let* v = Primitives.pvalue v |>
             Opt.to_result ~none: { kind = Etype; loc } in
  (* and an integer value *)
  Primitives.is_int v |> Opt.to_result ~none: { kind = Etype; loc}
