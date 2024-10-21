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

(* kind.ml : basic operations over kinds *)

open Deftypes
open Typerrors
   
(* The kind of an expression tells wheither it is:
 *- const: an expression that must be computed at compile-time;
 *- static: an expression that must be computed at instanciation time;
 *- any: a combinational expression;
 *- node: a stateful expression; either only discrete-time or continuous-time *)

(* The kind for function types:
 *- -V->                 -V|V->
 *- -S->                 -S|S->
 *- -A->                 -*|A->  any input; output is combinational
 *- -D->                 -*|D ->                      stateful (discrete)
 *- -C->                 -*|C ->                      stateful (continuous)
 *)

let rec is_const path =
  match path with
  | Pkind(Tfun(Tconst)) -> true
  | Pon(path, _) -> is_const path
  | _ -> false

let vkind_of_kind k = match k with | Tfun(v) -> v | Tnode _ -> Tany

(* kind from const or static *)
let kind_of_const is_const = Tfun(if is_const then Tconst else Tstatic)
let const_of_kind k =
  match k with
  | Tfun(Tconst) -> true
  | Tfun(Tstatic) -> false
  | Tfun _ | Tnode _ -> assert false

(* kind *)
let vkind k =
  match k with
  | Zelus.Kconst -> Deftypes.Tconst
  | Zelus.Kstatic -> Deftypes.Tstatic
  | Zelus.Kany -> Deftypes.Tany

(* order between kinds *)
let vkind_is_less_than actual_v expected_v =
  match actual_v, expected_v with
  | (Tconst, _) | (Tstatic, (Tstatic | Tany)) | (Tany, Tany) -> true
  | _ -> false

let left_right k =
  match k with
    | Tfun(k) ->
       (match k with
        | Tconst -> Tconst, Tconst | Tstatic -> Tstatic, Tstatic
        | Tany -> Tany, Tany)
    | Tnode _ -> Tany, Tany

let is_less_than actual_k expected_k =
  match actual_k, expected_k with
  | Tfun(k1), Tfun(k2) -> vkind_is_less_than k1 k2
  | Tfun _, Tnode _ -> true
  | Tnode k1, Tnode k2 when k1 = k2 -> true
  | _ -> false

let stateful = function | Tfun _ -> false | Tnode _ -> true

(* The sup of two kind. This function should be applied when *)
(* the sup exists; it should not raise an error *)
let sup k1 k2 =
  let sup k1 k2 = match k1, k2 with
  | (Tconst, _) -> k2 | (_, Tconst) -> k1
  | (Tstatic, _) -> k2 | (_, Tstatic) -> k1
  | (Tany, Tany) -> Tany in
  match k1, k2 with
  | (Tfun k1, Tfun k2) -> Tfun (sup k1 k2)
  | (Tfun _, _) -> k2
  | (_, Tfun _) -> k1
  | _ -> if k1 = k2 then k1 else assert false
                              
let sup_list l =
  match l with
  | [] -> Tfun(Tconst)
  | x :: l -> List.fold_left sup x l

let vinf v1 v2 =
  match v1, v2 with
  | (Tconst, _) -> v2 | (_, Tconst) -> v1
  | (Tstatic, _) -> v2 | (_, Tstatic) -> v1
  | _ -> v1

(* Check that a type belong to kind [ka]. The intuition is that:
 *- a function f of type t1 -{k1|k2}-> t2 must be such that:
 *- t1 is in kind k1 and t2 is in kind k2;
 *- it can only be applied in a context [ka]
 *- such that [ka <= k1]. *)
let rec in_kind ka { t_desc } =
  match t_desc with
  | Tvar -> true
  | Tproduct(ty_list) | Tconstr(_, ty_list, _) ->
     List.for_all (in_kind ka) ty_list
  | Tlink(ty_link) -> in_kind ka ty_link
  | Tvec(ty, _) -> in_kind ka ty
  | Tarrow { ty_kind; ty_arg; ty_res } ->
     let left_kfun, right_kfun = left_right ty_kind in
     in_kind left_kfun ty_arg && in_kind right_kfun ty_res
                               && vkind_is_less_than ka left_kfun

(* Kind inheritance. If the context has kind [expected_k] *)
(* and the local declaration is kind [vkind] *)
(* names will have the minimum of the two *)
let inherits expected_k vkind =
  match expected_k, vkind with
  | Tnode _, (Tconst | Tstatic) -> Tfun vkind
  | Tnode _, Tany -> expected_k
  | Tfun vfun, _ ->
     let vfun = match vfun, vkind with
       | (Tconst, _) | (_, Tconst) -> Tconst
       | (Tstatic, _) | (_, Tstatic) -> Tstatic
       | _ -> Tany in
     Tfun vfun
  
