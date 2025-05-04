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
type env = int Ident.Env.t

type exp = 
  | Sint of int (* [42] *)
  | Svar of Ident.t (* [n] *)
  | Sfrac of { num: exp; denom: int } (* [s / 42] *)
  | Sop of op * exp * exp (* [s * s | s + s | s - s] *)

(* add [div], [mod], [^] (2^n)] *)

and op = Splus | Sminus | Smult

(* a size constraint *)
type 'e constraints =
  | Rel of 'e eq (* e rel e *)
  | And of 'e constraints list (* [sc and ... and sc] *)
  | Let of (Ident.t * 'e) list * 'e constraints (* local binding *)
  | App of Ident.t * 'e list (* [f e1 ... en] *) 
  | Fix of (Ident.t * Ident.t list * 'e constraints) list * 'e constraints
  (* definition of mutually recursive functions on sizes *)
  | If of 'e constraints * 'e constraints * 'e constraints
  (* if c1 then c2 else c3 *)
  | Forall of Ident.t * 'e * 'e constraints
  (* forall i in e .. e do c *)
  | True | False
  | Loc of Location.t * 'e constraints
  (* localisation of errors *)

and file_name = string (* name of the file *)

and 'a eq = { rel: rel; lhs: 'a; rhs: 'a }
and rel = Eq | Lt | Lte

let constraint_is_true sc = match sc with | True -> true | _ -> false

(* the stack of size constraints *)
type stack_of_size_constraint =
  { stack: exp constraints Stack.t;
    mutable current: exp constraints }

(* the stack of constraints *)
let c_stack : stack_of_size_constraint =
  { stack = Stack.create (); current = True }

(* A size function [fun <<n1,...,nk>>. e] has type [<<n1,...,nk>>.t with c] *)
(* the body is typed with an empty constraint pushed on to of [c_stack] *)

(* empty the stack of constraints *)
let clear () =
  Stack.clear c_stack.stack;
  c_stack.current <- True

(* push an empty constraint *)
let push () =
  Stack.push c_stack.current c_stack.stack;
  c_stack.current <- True
let add c =
  c_stack.current <-
    match c_stack.current with | True -> c | c_old -> And [c;c_old]
(* pop/restore the previous one *)
let pop () =
  let c = c_stack.current in
  let c_old = Stack.pop c_stack.stack in
  c_stack.current <- c_old;
  c
(* the stack of constraints is empty *)
let is_empty () =
  let c = c_stack.current in
  Stack.is_empty c_stack.stack && constraint_is_true c
(* sequence of constraints *)
let to_seq () =
  let l = Stack.to_seq c_stack.stack in
  Seq.cons c_stack.current l 

