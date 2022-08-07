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

(* index in a loop body *)
type index =
  (* [xi in e by e'] means that in the i-th iteration, xi = e.(e' * i) *)
  | Vinput : { ve : pvalue array; by : int option } -> index
  (* [j in e0 to e1 or j in e0 downto e1] means that in the i-th iteration *)
  (* j = i + e0 in the first case; j = e1 - i in the second with i in [0..n-1] *)
  | Vindex : { ve_left : int; ve_right : int; dir : bool } -> index

      
(* given an index environment [i_env = [x1\v1,...,xk\vk]]
 *- and index [i: [0..n-1]], returns an environment [l_env]
 *- where:
 *-  - if i_env(x) = Vinput { ve; by } then l_env(x) = ve.(by * i)
 *-  - if i_env(x) = Vindex { ve_left; ve_right; dir } then
                               l_env(x) = ve_left + i  if dir
                               l_env(x) = ve_right -i  otherwise *)
let geti_env i_env i =
  let open Opt in
  let entry v = { cur = v; last = None; default = None } in
  Env.fold
    (fun x v acc ->
      match v with
      | Vbot | Vnil as v -> Env.add x (entry v) acc
      | Value(v) ->
         match v with
         | Vindex { ve_left; ve_right; dir } ->
            let i = if dir then ve_left + i else ve_right - i in
            Env.add x (entry (Value(Vint(i)))) acc
         | Vinput { ve; by } ->
            let i = match by with
              | None -> i | Some(v) -> i + v in
            let vi = Primitives.geti ve i in
            match vi with | None -> acc | Some(vi) -> Env.add x (entry vi) acc)
    i_env Env.empty
      
(* [x_to_last_x env acc_env = acc_env'] such that for every [x] *)
(* in Dom(acc_env), replace entry [x\...] by [x\{ last = v }] *)
(* if env(x) = { cur = v } *)
let x_to_last_x local_env acc_env =
  Sdebug.print_ienv "x_to_last_x: local_env:" local_env;
  Sdebug.print_ienv "x_to_last_x (before): acc_env:" acc_env;
  let acc_env =
    Env.mapi
    (fun x ({ default }) ->
      let v = Find.find_value_opt x local_env in
      { cur = Vbot; last = v; default })
    acc_env in
  Sdebug.print_ienv "x_to_last_x (after): acc_env" acc_env; acc_env

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

let forward_i_without_exit_condition:
      int -> (int -> (value ientry Env.t as 'a) -> state ->
              ('a * 'a * state, 'e) Result.t) -> 'a -> state ->
      ('a list * 'a * state, 'e) Result.t =
  fun n f acc_env0 s ->
  let rec for_rec i acc_env s =
    Sdebug.print_ienv "Debut iteration" acc_env;
    if i = n then return ([], acc_env, s)
    else
      let* f_env, acc_env, s = f i acc_env s in
      Sdebug.print_ienv "Env iteration" f_env;
      let* env_list, acc_env, s = for_rec (i+1) acc_env s in
      return (f_env :: env_list, acc_env, s) in
  for_rec 0 acc_env0 s

(* instantaneous for loops with an exit condition *)
(* this condition must be combinational *)
let forward_i_with_exit_condition loc n write f cond acc_env0 s =
  let rec for_rec i acc_env s =
    if i = n then return ([], acc_env, s)
    else
      let* f_env, acc_env, s = f i acc_env s in
      let* v = cond f_env in
      match v with
      | Vbot ->
         let f_env = bot_env write in return ([f_env], acc_env, s) 
      | Vnil ->
         let f_env = nil_env write in return ([f_env], acc_env, s)
      | Value(v) ->
           let* b =
             Opt.to_result ~none:{ kind = Etype; loc = loc } (bool v) in
           let* env_list, acc_env, s =
             if b then for_rec (i+1) acc_env s
             else return ([], acc_env, s) in
           return (f_env :: env_list, acc_env, s) in
  for_rec 0 acc_env0 s

(* main entry functions *)

(* parallel loop: the step function is iterated with different states;
 *- output is an array. *)
let foreach sbody env i_env s_list =
  let* ve_list, s_list =
    foreach_i
      (fun i se ->
        let env = Env.append (geti_env i_env i) env in
        sbody env se) s_list in
  let ve_list = Primitives.slist ve_list in
  return (Primitives.lift (fun v -> Varray(Array.of_list v)) ve_list, s_list)

(* Parallel loop with accumulation *)
(* every step computes an environment. The output [v/x] at iteration [i] *)
(* becomes an input [v/last x] for iteration [i+1] *)
let foreach_with_accumulation_i sbody env i_env acc_env0 s_list =
  let* env_list, acc_env, s_list =
    foreach_with_accumulation_i
      (fun i acc_env s ->
        let env = Env.append (geti_env i_env i)
                    (Env.append acc_env env) in
        let* local_env, s = sbody env s in
        (* every entry [x\v] becomes [x \ { cur = bot; last = v }] *)
        let acc_env = x_to_last_x local_env acc_env in
        return (local_env, acc_env, s))
      acc_env0 s_list in
  return (env_list, acc_env0, s_list)

(* hyperserial loop: the step function is iterated on the very same state;
 *- output is the last value *)
let forward sbody env i_env n default s =
  forward_i n default
      (fun i se ->
        let env = Env.append (geti_env i_env i) env in
        sbody env se) s

(* [i_env] is the environment for indexes; [acc_env_0] is the environment *)
(* for accumulated variables; [env] is the current environment *)
let forward_i_without_exit_condition sbody env i_env acc_env0 n s =
  forward_i_without_exit_condition n
      (fun i acc_env se ->
        Sdebug.print_ienv "Forward: Env:" env;
        Sdebug.print_ienv "Forward: Env acc (before):" acc_env;
        let env = Env.append (geti_env i_env i)
                    (Env.append acc_env env) in
        let* local_env, s = sbody env s in
        (* every entry [x\v] becomes [x \ { cur = bot; last = v }] *)
        let acc_env = x_to_last_x local_env acc_env in
        Sdebug.print_ienv "Forward: Env acc (after):" acc_env;
        return (local_env, acc_env, s))
      acc_env0 s

let forward_i_with_exit_condition loc write sbody cond env i_env acc_env0 n s =
  forward_i_with_exit_condition loc n write
      (fun i acc_env se ->
        Sdebug.print_ienv "Forward: Env:" env;
        Sdebug.print_ienv "Forward: Env acc (before):" acc_env;
        let env = Env.append (geti_env i_env i)
                    (Env.append acc_env env) in
        let* local_env, s = sbody env s in
        (* every entry [x\v] becomes [x \ { cur = bot; last = v }] *)
        let acc_env = x_to_last_x local_env acc_env in
        Sdebug.print_ienv "Forward: Env acc (after):" acc_env;
        return (local_env, acc_env, s))
      cond acc_env0 s
