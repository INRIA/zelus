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

(* Elimination of copy variables [x = y] defined in non recursive let/in *)

open Misc
open Ident
open Zelus
open Deftypes

(* a map: ident -> ident *)
(* bounded names are renamed; otherwise, they stay unchanged *)
type acc = Ident.t Env.t

let empty = Env.empty

let rec remove_copies acc ({ eq_desc; eq_loc } as eq) =
  match eq_desc with
  | EQeq({ pat_desc = Evarpat(x) }, { e_desc = Evar(y) }) ->
     { eq with eq_desc = EQempty }, Env.add x y acc
  | EQand { ordered; eq_list } ->
     let eq_list, acc = 
       Util.mapfold remove_copies acc eq_list in
     Aux.set_loc_if_not_empty eq_loc (Aux.par_t ordered eq_list), acc
  | _ -> raise Mapfold.Fallback
     
let expression funs acc ({ e_desc; e_loc } as e) =
  match e_desc with
  | Evar(x) ->
     let x = try Env.find x acc with Not_found -> x in 
     { e with e_desc = Evar(x) }, acc 
  | Elet(leq, e_let) ->
     let leq, acc = Mapfold.leq_it funs acc leq in
     let e_let, acc = Mapfold.expression_it funs acc e_let in
     { (Aux.e_let leq e_let) with e_loc }, acc
  | _ -> raise Mapfold.Fallback
						
(* Local declarations *)
let leq_t funs acc ({ l_rec; l_eq } as l) =
  let l_eq, acc = Mapfold.equation_it funs acc l_eq in
  let l_eq, acc = if l_rec then l_eq, acc else remove_copies acc l_eq in
  { l with l_eq }, acc

let program genv p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with
      expression; leq_t; global_funs } in
  let p, _ = Mapfold.program_it funs empty p in
  p
