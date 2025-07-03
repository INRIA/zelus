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

(* Sets the sort of variables in the environment. This pass must *)
(* be done at the very end, in particular after normalisation and typing *)

open Location
open Ident
open Zelus
open Deftypes
open Mapfold

let set_sort mkind x acc =
  let { t_sort } as tentry = 
    Env.find_stop_if_unbound "Error in pass Set_sorts" x acc in
  tentry.t_sort <- Deftypes.sort_mem mkind t_sort

let set_init x acc =
  let { t_sort } as tentry = 
    Env.find_stop_if_unbound "Error in pass Set_sorts" x acc in
  tentry.t_sort <- Deftypes.init_in_eq t_sort

let set_shared_variables acc names =
  S.iter
    (fun x -> 
      let { t_sort } as tentry = 
        Env.find_stop_if_unbound "Error in pass Set_sorts" x acc in
      if Deftypes.is_val t_sort then tentry.t_sort <- Deftypes.Sort_var) names

let build global_funs acc p_env =
  let acc = Env.append p_env acc in p_env, acc

(* [acc] is an environment *)
let equation funs acc eq =
  let { eq_desc; eq_write } as eq, acc = Mapfold.equation funs acc eq in
  match eq_desc with
  (* [x = up(e)] *)
  | EQeq({ pat_desc = Evarpat(x) }, { e_desc = Eop(Eup _, _) }) ->
     set_sort Deftypes.Zero x acc;
     eq, acc
  (* [x = horizon(e)] *)
  | EQeq({ pat_desc = Evarpat(x) }, { e_desc = Eop(Ehorizon _, _) }) ->
     set_sort Deftypes.Horizon x acc;
     eq, acc
  (* [init x = e] *)
  | EQinit(x, e) -> set_init x acc; eq, acc
  (* [der x = e] *)
  | EQder { id } -> set_sort Deftypes.Cont id acc; eq, acc
  | EQif _ | EQmatch _ ->
     (* variables in [eq_write] are shared *)
     let w_names = (Defnames.names S.empty eq_write) in
     set_shared_variables acc w_names;
     eq, acc
  | _ -> eq, acc


let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = { Mapfold.default_global_funs with build } in
  let funs =
    { Mapfold.defaults with equation;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs Env.empty p in
  { p with p_impl_list = p_impl_list }
