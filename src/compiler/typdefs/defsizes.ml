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

(* definition of sizes and size constraints *)

type t = 
  | Sint of int (* [42] *)
  | Svar of Ident.t (* [n] *)
  | Sfrac of { num: t; denom: int } (* [s / 42] *)
  | Sop of op * t * t (* [s * s | s + s | s - s] *)

and op = Splus | Sminus | Smult

(* a size constraint *)
type eq =
  | Rel of { rel: rel; lhs: t; rhs: t } (* t rel e *)
  | Let of (Ident.t * t) list * eq

and rel = Eq | Lt | Lte

(* the stack of size constraints *)
type c_stack = eq list Stack.t

(* the stack of constraints *)
let c_stack : c_stack = Stack.create ()

(* A size function [fun <<n1,...,nk>>. e] has type [<<n1,...,nk>>.t with c] *)
(* the body is typed with an empty constraint pushed on to of [c_stack] *)

(* empty the stack of constraints *)
let clear () = Stack.clear c_stack

(* push an empty constraint *)
let push () = Stack.push [] c_stack
(* pop/restore the previous one *)
let pop () = Stack.pop c_stack

