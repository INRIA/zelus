(***********************************************************************)
(*                                                                     *)
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

(** Names written in a block *)
type defnames = 
  { dv: Ident.S.t;  (* [x = ...] *)
    di : Ident.S.t; (* [init x = ...] *)
    der: Ident.S.t; (* [der x = ...] *)}

(* set of names. *)
let names acc { dv; di; der } =
  Ident.S.union dv (Ident.S.union di (Ident.S.union der acc))
let cur_names acc { dv; di } = Ident.S.union dv (Ident.S.union di acc)

(* empty set of defined names *)
(** Making values *)
let empty = { dv = Ident.S.empty; di = Ident.S.empty; der = Ident.S.empty }
let singleton x = { empty with dv = Ident.S.singleton x }
let union { dv = dv1; di = di1; der = der1 }
      { dv = dv2; di = di2; der = der2  } =
  { dv = Ident.S.union dv1 dv2;
    di = Ident.S.union di1 di2;
    der = Ident.S.union der1 der2 }
(* removes names from [names] *)
let diff { dv; di; der } names =
  { dv = Ident.S.diff dv names;
    di = Ident.S.diff di names;
    der = Ident.S.diff der names }
(* replaces name x in [dv, di, der] by h(x) *)
let subst { dv; di; der } h =
  let subst names =
    Ident.S.map (fun n -> try Ident.Env.find n h with | Not_found -> n) names in
  { dv = subst dv;
    di = subst di;
    der = subst der }
