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

(* distribution of tuples and records *)
(* [(p1,...,pn) = (e1,...,en)] = [p1 = e1 and ... and pn = en] *)
(* [{ m1 = p1; ...; mn = pn } = { m1 = e1;...; mn = en }] = *)
(*    [p1 = e1 and ... and pn = en] *)

open Zelus

let empty = ()

(* matching. Translate [(p1,...,pn) = (e1,...,en)] into *)
(* [p1 = e1 and ... and pn = en] *)
let rec matching eq_list ({ pat_desc } as p) ({ e_desc } as e) =
  let order { label = l1 } { label = l2 } = Lident.compare l1 l2 in
  match pat_desc, e_desc with
  | Etuplepat(p_list), Etuple(e_list) ->
     List.fold_left2 matching eq_list p_list e_list
  | Erecordpat(l_p_list), Erecord(l_e_list) ->
     let l_p_list = List.sort order l_p_list in
     let l_e_list = List.sort order l_e_list in
     matching_record_list eq_list l_p_list l_e_list
  | _ -> (Aux.eq_make p e) :: eq_list

and matching_record_list eq_list l_p_list l_e_list =
  match l_p_list, l_e_list with
  | [], [] -> eq_list
  | [], { arg } :: l_e_list -> Aux.wildpat_eq arg :: eq_list
  | { label = l1; arg = p } :: l_p_list, { label = l2; arg } :: l_e_list ->
     let v = Lident.compare l1 l2 in
     if v = 0 then matching eq_list p arg
     else assert false
| _ -> assert false

let equation funs acc eq =
  let ({ eq_desc } as eq), acc = Mapfold.equation funs acc eq in
  let eq = match eq_desc with
    | EQeq(p, e) -> Aux.par (matching [] p e) | _ -> eq in
  eq, acc
 
let program genv p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; global_funs } in
  let p, _ = Mapfold.program_it funs empty p in
  p

