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

(* Identify assignments to shared variables *)
(* After this transformation, equations on structured patterns *)
(* like [pat = e] are such that no variable in [pat] *)
(* is shared nor a memory. All equations on those variables *)
(* are then of the form [x = e] *)

open Location
open Ident
open Zelus
open Aux
open Mapfold

(* An equation [pat = e] where [xi in pat] is shared is rewritten into *)
(* [local x_copyi,... do pat_copy = e and xi = x_copyi and ...] *)


let fresh () = Ident.fresh "copy"

let empty = S.empty

(* Makes a copy of a pattern [p] when it contains a shared variable [x] *)
(* introduce auxilary equations [x = x_copy] for every name in [dv] *)
let copy_pattern dv p e =
  let var_ident global_funs ((dv, env) as acc) x =
    if S.mem x dv then if Env.mem x env then Env.find x env, acc
                       else let x_copy = fresh () in
                            x_copy, (dv, Env.add x x_copy env)
    else x, acc in
  let global_funs = { Mapfold.default_global_funs with var_ident } in
  let funs = { Mapfold.defaults with global_funs } in
  let p, (_, env) = Mapfold.pattern funs (dv, Env.empty) p in
  let vardec_list, x_x_copy_list =
    Env.fold
      (fun x x_copy (vardec_list, x_x_copy_list) ->
        Aux.vardec x_copy false None None :: vardec_list,
        Aux.id_eq x (Aux.var x_copy) :: x_x_copy_list) env ([], []) in
  Aux.eq_local_vardec
    vardec_list (Aux.eq_make p e :: x_x_copy_list)

let pattern funs acc p = p, acc
let built_it global_funs acc p_env = p_env, acc
 
(* [dv] is the set of names possibly written in [eq] and shared, that is *)
(* they appear on at least one branch of a conditional *)
(* [acc] is a set of names *)
let rec equation funs acc ({ eq_desc; eq_write } as eq) =
  match eq_desc with
  | EQeq({ pat_desc = Evarpat(x) } as p, e) ->
     let e, acc = Mapfold.expression funs acc e in
     { eq with eq_desc = EQeq(p, e) }, acc
  | EQeq(p, e) ->
     let e, acc = Mapfold.expression funs acc e in
     copy_pattern acc p e, acc
  | EQif { e; eq_true; eq_false } ->
     let eq_true, acc = equation funs eq_write.dv eq_true in
     let eq_false, acc = equation funs eq_write.dv eq_false in
     { eq with eq_desc = EQif {e; eq_true; eq_false } }, acc
  | EQmatch({ e; handlers } as m) ->
     let e, acc = Mapfold.expression funs acc e in
     (* variables in [eq_write] are shared *)
     let handlers, acc =
       Util.mapfold (Mapfold.match_handler_eq funs) eq_write.dv handlers in
       { eq with eq_desc = EQmatch { m with e; handlers } }, acc
  | EQpresent({ handlers; default_opt }) ->
     (* variables in [eq_write] are shared *)
     let handlers, acc = 
       Util.mapfold (Mapfold.present_handler_eq funs) eq_write.dv handlers in
     let default_opt, acc = 
       Mapfold.default_t (equation funs) acc default_opt in
     { eq with eq_desc = EQpresent { handlers; default_opt } }, acc
  | EQautomaton({ handlers; state_opt } as a) ->
     (* variables in [eq_write] are shared *)
     let state_opt, acc = 
       Util.optional_with_map (Mapfold.state funs) acc state_opt in
     let handlers, acc = 
       Util.mapfold (Mapfold.automaton_handler funs) eq_write.dv handlers in
     { eq with eq_desc = EQautomaton({ a with handlers; state_opt }) }, acc
  | _ -> Mapfold.equation funs acc eq

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = { Mapfold.default_global_funs with build } in
  let funs =
    { Mapfold.defaults with pattern; equation;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs S.empty p in
  { p with p_impl_list = p_impl_list }
