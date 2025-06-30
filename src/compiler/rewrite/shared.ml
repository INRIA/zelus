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

(* Identify assignments to shared variables and state variables *)
(* (memories) *)
(* After this transformation, equations on structured patterns *)
(* like [pat = e] are such that no variable in [pat] *)
(* is shared nor a is a state variable. All equations on those variables *)
(* are then of the form [x = e] *)

open Location
open Ident
open Zelus
open Aux
open Mapfold

let fresh () = Ident.fresh "copy"

(* An equation [pat = e] where the [xi_j in pat]_j are shared *)
(* or state variables is rewritten *)
(* [local x_copyi,... do pat_copy = e and (xi_j = x_copyi_j)_j] *)

(* Computes the set of shared memories and state variables from *)
(* an environment. Add it to the current set of [acc] *)
let build global_funs acc p_env = 
  (* add shared and state variables *)
  let open Deftypes in
  let add x sort acc =
    match sort with 
    | Sort_val -> acc | Sort_var | Sort_mem _ -> S.add x acc in
  let acc = 
    Env.fold (fun x { t_sort } acc -> add x t_sort acc) p_env acc in
  p_env, acc
 
(* Makes a copy of a pattern [p] when it contains a shared variable [x] *)
(* introduce auxilary equations [x = x_copy] for every name in [dv] *)
let copy_pattern (acc as dv) p e =
  let var_ident global_funs ((dv, env) as acc) x =
    if S.mem x dv then if Env.mem x env then Env.find x env, acc
                       else let x_copy = fresh () in
                            x_copy, (dv, Env.add x x_copy env)
    else x, acc in
  let global_funs = { Mapfold.default_global_funs with var_ident } in
  let funs = { Mapfold.defaults with global_funs } in
  let p, (_, env) = Mapfold.pattern_it funs (dv, Env.empty) p in
  let vardec_list, x_x_copy_list =
    Env.fold
      (fun x x_copy (vardec_list, x_x_copy_list) ->
        Aux.vardec x_copy false None None :: vardec_list,
        Aux.id_eq x (Aux.var x_copy) :: x_x_copy_list) env ([], []) in
  Aux.eq_local_vardec
    vardec_list (Aux.eq_make p e :: x_x_copy_list)

(* [acc] is the set of names that are shared *)
let equation funs acc ({ eq_desc; eq_write } as eq) =
  match eq_desc with
  | EQeq({ pat_desc = Evarpat(x) } as p, e) ->
     let e, _ = Mapfold.expression_it funs acc e in
     { eq with eq_desc = EQeq(p, e) }, acc
  | EQeq(p, e) ->
     let e, _ = Mapfold.expression_it funs acc e in
     copy_pattern acc p e, acc
  | EQif { e; eq_true; eq_false } ->
     (* variables in [eq_write] are shared *)
     let e, _ = Mapfold.expression_it funs acc e in
     let acc = Defnames.names acc eq_write in
     let eq_true, acc = Mapfold.equation_it funs acc eq_true in
     let eq_false, acc = Mapfold.equation_it funs acc eq_false in
     { eq with eq_desc = EQif {e; eq_true; eq_false } }, acc
  | EQmatch({ e; handlers } as m) ->
     let e, _ = Mapfold.expression_it funs acc e in
     (* variables in [eq_write] are shared *)
     let acc = Defnames.names acc eq_write in
     let handlers, acc =
       Util.mapfold (Mapfold.match_handler_eq_it funs) acc handlers in
       { eq with eq_desc = EQmatch { m with e; handlers } }, acc
  | _ -> raise Mapfold.Fallback


let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = { Mapfold.default_global_funs with build } in
  let funs =
    { Mapfold.defaults with equation;  set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs S.empty p in
  { p with p_impl_list = p_impl_list }
