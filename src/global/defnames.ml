(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2025 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Names written in a block *)
open Ident
type defnames = 
  { dv: S.t;  (* [x = ...] *)
    di : S.t; (* [init x = ...] *)
    der: S.t; (* [der x = ...] *)}

(* set of names. *)
let names acc { dv; di; der } =
  S.union dv (S.union di (S.union der acc))
let cur_names acc { dv; di } = S.union dv (S.union di acc)

(* empty set of defined names *)
(* Making values *)
let empty = { dv = S.empty; di = S.empty; der = S.empty }
let is_empty { dv; di; der } =
  (S.is_empty dv) && (S.is_empty di) && (S.is_empty der)
let singleton x = { empty with dv = S.singleton x }
let union { dv = dv1; di = di1; der = der1 }
      { dv = dv2; di = di2; der = der2  } =
  { dv = S.union dv1 dv2;
    di = S.union di1 di2;
    der = S.union der1 der2 }
(* removes names from [names] *)
let diff { dv; di; der } names =
  { dv = S.diff dv names;
    di = S.diff di names;
    der = S.diff der names }
(* replaces name x in [dv, di, der] by h(x) *)
let subst { dv; di; der } h =
  let subst names =
    S.map (fun n -> try Ident.Env.find n h with | Not_found -> n) names in
  { dv = subst dv;
    di = subst di;
    der = subst der }
