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

(* Simple cost function for an expression *)
(* [max] is the maximum allowed cost of [e] *)
(* raise Exit if the cost is greater than [max] *)

open Ident
open Zelus

(* cost of operators *)
let rec operator acc op =
  let acc = match op with
    | Efby -> acc - 2
    | Eunarypre -> acc - 2
    | Eifthenelse -> acc - 1
    | Eminusgreater -> acc - 2
    | Eseq -> acc 
    | Erun _ -> acc 
    | Eatomic -> acc 
    | Etest -> acc - 1
    | Eup _ -> acc - 2
    | Einitial -> acc - 2
    | Eperiod -> acc - 2
    | Ehorizon _ -> acc - 2
    | Edisc -> acc - 2
    | Earray(op) -> array_operator acc op in
  if acc <= 0 then raise Exit else acc

and array_operator acc op =
  let v = match op with
    | Earray_list -> 1
    | Econcat -> 1
    | Eget -> 1
    | Eget_with_default -> 1
    | Eslice -> 1
    | Eupdate -> 1
    | Etranspose -> 1
    | Eflatten -> 1
    | Ereverse -> 1 in
  let acc = acc - v in
  if acc <= 0 then raise Exit else acc

let expression funs acc ({ e_desc } as e) =
  let e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eop(op, _) ->
     let acc = operator acc op in
     e, acc
  | Eapp _ -> e, acc - 2
  | _ -> e, acc

(* the main entry function *)
let result max r =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; global_funs } in
  try
    let _ = Mapfold.result_it funs max r in true
  with 
  | Exit -> false
