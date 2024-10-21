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

(* free variables, defined variables. Writes and env. must be correct *)
(* The definition below considers that [x] and [y] are free in *)
(* equation [...x... = ... y...]. *)

open Ident
open Zelus
open Mapfold

type acc = { bounded: S.t; current: S.t; last: S.t }

let empty = { bounded = S.empty; current = S.empty; last = S.empty }

let build global_funs ({ bounded } as acc) p_env =
  p_env,
  { acc with bounded = Env.fold (fun x _ acc -> S.add x acc) p_env bounded }

let var_ident global_funs ({ bounded; current; last } as acc) x =
  let current = if S.mem x bounded || S.mem x current
                then current else S.add x current in
  x, { acc with current }

let last_ident global_funs ({ bounded; last } as acc) ({ id } as l) =
  let last = if S.mem id bounded || S.mem id last
             then last else S.add id last in
  l, { acc with last }

let init_ident global_funs acc x = x, acc

let der_ident global_funs acc x = x,acc

let pattern funs acc pat = pat, acc

let funs =
  let global_funs =
    { Mapfold.default_global_funs with build; var_ident; 
                                       last_ident; init_ident; der_ident } in
  { Mapfold.defaults with pattern; global_funs }

type t =
  { lv: S.t; (* last variables *)
    v: S.t; (* variables *)
  }

let expression { lv; v } e =
  let _, { last; current } =
    Mapfold.expression_it funs
      { empty with last = lv; current = v } e in
  { lv = last; v = current }

let equation eq =
  let _, { last; current } =
    Mapfold.equation_it funs empty eq in
  { lv = last; v = current }
