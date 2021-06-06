(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
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
   
(** The kind of an expression tells wheither it is:
 *- S: a static expression;
 *- F: a combinational expression;
 *- N: a stateful expression *)

(** The kind for function types:
 *- -S->                 -S|S->
 *- -F->                 -*|F->  any input; output is combinational
 *- -N->                 -*|N ->                      stateful
 *)

(* kind from a sort *)
let kind_of = function | Sstatic -> Tstatic | _ -> Tfun
                                                 
(* order between kinds *)
let is_less_than actual_k expected_k =
  match actual_k, expected_k with
  | (Tstatic, _) | (Tfun, (Tfun | Tnode)) | (Tnode, Tnode) -> true
  | _ -> false

(** Entry function for comparison *)
let less_than loc actual_k expected_k =
  if not (is_less_than actual_k expected_k)
  then error loc (Ekind_clash(actual_k, expected_k))

(* The sup of two kind. This function is only applied when *)
(* the sup exists; hence it should raise no error *)
let sup k1 k2 =
  match k1, k2 with
  | (Tstatic, _) -> k2 | (_, Tstatic) -> k1
  | (Tfun, _) -> k2 | (_, Tfun) -> k1
  | _ -> Tnode
                              
let sup_list l =
  match l with
  | [] -> Tstatic
  | x :: l -> List.fold_left sup x l
  					      
(* Check that a type belong to kind [k]. The intuition is this:
 *- a function type -{k1|k2}-> must be applied in a context [ka]
 *- such that [ka < k1]. *)
let rec in_kind k { t_desc } =
  match t_desc with
  | Tvar -> true
  | Tproduct(ty_list) | Tconstr(_, ty_list, _) ->
     List.for_all (in_kind k) ty_list
  | Tlink(ty_link) -> in_kind k ty_link
  | Tarrow(kfun, t1, t2) ->
     match k, kfun with
     | (Tstatic, _) | (Tfun, Tfun) ->
        (in_kind kfun t1) && (in_kind kfun t2)
     | _ -> false

