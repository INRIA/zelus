(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2022 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* The different form of step functions for for loops *)

open Error
open Monad
open Result
open Ident
open Genv
open Value
open Find
open Primitives
open Match

(* [x_to_last_x env acc_env = acc_env'] such that for every [x] *)
(* in Dom(acc_env), replace entry [x\...] by [x\{ last = v }] *)
(* if env(x) = { cur = v } *)
let x_to_last_x local_env acc_env =
  Env.mapi
    (fun x ({ default }) ->
      let v = Find.find_value_opt x local_env in
      { cur = Vbot; last = v; default })
    acc_env

(* loop iteration *)
(* parallel for loops; take a list of states *)
let foreach_i : (int -> 's -> ('r * 's, 'error) Result.t) -> 's list
                -> ('r list * 's list, 'error) Result.t =
  fun f s_list ->
  let rec for_rec i s_list =
    match s_list with
    | [] -> return ([], [])
    | s :: s_list ->
       let* x, s = f i s in
       let* x_list, s_list = for_rec (i+1) s_list in
       return (x :: x_list, s :: s_list) in
  for_rec 0 s_list

(* the same parallel loop except that [f] takes also an accumulator *)
(* that is passed from iteration [i] to iteration [i+1] *)
let foreach_with_accumulation_i f acc_0 s_list =
  let rec for_rec i acc s_list =
    match s_list with
    | [] -> return ([], acc, [])
    | s :: s_list ->
       let* x, acc, s = f i acc s in
       let* x_list, acc, s_list = for_rec (i+1) acc s_list in
       return (x :: x_list, acc, s :: s_list) in
  for_rec 0 acc_0 s_list

(* instantaneous for loops; take a single state and iterate on it *)
let forward_i n default f s =
  let rec for_rec default i s =
    if i = n then return (default, s)
    else
      let* v, s = f i s in
      for_rec v (i+1) s in
  for_rec default 0 s

let forward_i_without_stop_condition n f acc_env0 s =
  let rec for_rec i acc_env s =
    if i = n then return ([], acc_env0, s)
    else
      let* f_env, acc_env, s = f i acc_env s in
      let* env_list, acc_env, s = for_rec (i+1) acc_env s in
      return (f_env :: env_list, acc_env, s) in
  for_rec 0 acc_env0 s

(* instantaneous for loops with a stopping condition *)
let forward_i_with_stop_condition loc n write f cond (s, sc) =
  let rec for_rec i (s, sc) =
    if i = n then return ([], Env.empty, (s, sc))
    else
      let* f_env, s = f i s in
      let* v, sc = cond f_env sc in
      match v with
      | Vbot ->
         let f_env = bot_env write in return ([f_env], f_env, (s, sc)) 
      | Vnil ->
         let f_env = nil_env write in return ([f_env], f_env, (s, sc))
      | Value(v) ->
           let* b =
             Opt.to_result ~none:{ kind = Etype; loc = loc } (bool v) in
           let* env_list, env, s_sc =
             if b then for_rec (i+1) (s, sc)
             else return ([f_env], f_env, (s, sc)) in
           return (f_env :: env_list, env, s_sc) in
  for_rec 0 (s, sc)

(* parallel loop: the step function is iterated with different states;
 *- output is an array. *)
let foreach sbody env l_env s_list =
  let* ve_list, s_list =
    foreach_i
      (fun i se ->
        let env = Env.append env (Combinatorial.geti_env l_env i) in
        sbody env se) s_list in
  let ve_list = Primitives.slist ve_list in
  return (Primitives.lift (fun v -> Varray(Array.of_list v)) ve_list, s_list)

(* Parallel loop with accumulation *)
(* every step computes an environment. The output [v/x] at iteration [i] *)
(* becomes an input [v/last x] for iteration [i+1], for all x in init_names *)
(* the output is computed using the [out] function. *)
let foreach_with_accumulation_i
      sbody env l_env acc_env0 s_list =
  let* env_list, acc_env, s_list =
    foreach_with_accumulation_i
      (fun i acc_env s ->
        let env = Env.append env
                    (Env.append acc_env (Combinatorial.geti_env l_env i)) in
        let* env, local_env, s = sbody env s in
        (* every entry [x\v] becomes [x \ { cur = bot; last = v }] *)
        let acc_env = x_to_last_x local_env acc_env in
        return (env, acc_env, s))
      acc_env0 s_list in
  return (env_list, acc_env0, s_list)

(* hyperserial loop: the step function is iterated on the very same state;
 *- output is the last value *)
let forward sbody env l_env n default s =
  forward_i n default
      (fun i se ->
        let env = Env.append env (Combinatorial.geti_env l_env i) in
        sbody env se) s

(* [l_env] is the environment for indexes; [acc_env_0] is the environment *)
(* for accumulated variables; [env] is the current environment *)
let forward_i_without_stop_condition sbody env l_env acc_env0 n s =
  forward_i_without_stop_condition n
      (fun i acc_env se ->
        let env = Env.append env
                    (Env.append acc_env0 (Combinatorial.geti_env l_env i)) in
        let* env, local_env, s = sbody env s in
        (* every entry [x\v] becomes [x \ { cur = bot; last = v }] *)
        let acc_env = x_to_last_x local_env acc_env in
        return (env, acc_env, s))
      acc_env0 s
