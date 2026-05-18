(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2026 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* The evaluation functions for for loops. *)

open Error
open Monad
open Result
open Ident
open Genv
open Value
open Find
open Primitives
open Match

(* type error for arrays *)
let typ_error_array = Etype(Some(Etyp_array))

let (let+) v f =
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) -> f v

let (and+) v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(v1, v2)

(* index in a loop body *)
type index =
  (* [xi in e by e'] means that in the i-th iteration, xi = e.(e' * i) *)
  | Vinput of { ve : pvalue array; by : int option }
  (* [j in e0 to e1 or j in e0 downto e1] means that in the i-th iteration *)
  (* j = i + e0 in the first case; j = e1 - i in the second with i in [0..n-1] *)
  | Vindex of { ve_left : int; ve_right : int; dir : bool }


(* given an index environment [i_env = [x1\v1,...,xk\vk]]
 *- and index [i: [0..n-1]], returns an environment [l_env]
 *- where:
 *-  - if i_env(x) = Vinput { ve; by } then l_env(x) = ve.(by * i)
 *-  - if i_env(x) = Vindex { ve_left; ve_right; dir } then
                               l_env(x) = ve_left + i  if dir
                               l_env(x) = ve_right -i  otherwise *)
let geti loc v i =
  match v with
  | Vflat(v) ->
     let n = Array.length v in
     if (i < n) && (i >= 0) then return (Value(v.(i)))
     else error { kind = Earray_index { size = n; index = i }; loc }
  | Vmap { m_length; m_u } ->
     if (i < m_length) && (i >= 0) then
       let* v = m_u i in return (Value(v))
     else error { kind = Earray_index { size = m_length; index = i }; loc }

let geti_env loc i_env i =
  let s_env = Env.to_seq i_env in
  let entry v = { empty with cur = Some(v) } in
  Result.seqfold
    (fun acc (x, v) ->
      match v with
      | Vindex { ve_left; ve_right; dir } ->
         let i = if dir then ve_left + i else ve_left - i in
         return (Env.add x (entry (Value(Vint(i)))) acc)
      | Vinput { ve; by } ->
         let i = match by with
           | None -> i | Some(v) -> i + v in
         let* vi = geti loc ve i in
         return (Env.add x (entry vi) acc))
    Env.empty s_env

 
(* [x_to_last_x acc_env local_env] returns [acc_env'] where *)
(* [Dom(acc_env) = Dom(acc_env')] and *)
(* [acc_env'(x) = { cur = bot; last = v }] if [local_env(x) = v] *)
let x_to_lastx acc_env local_env =
  let acc_env =
    Env.mapi
      (fun x entry ->
        let v = Find.find_value_opt x local_env in
        { entry with cur = Some(Vbot); last = v })
      acc_env in
  acc_env

(* copy [last x] into [x] *)
let lastx_to_x acc_env =
  Env.mapi
    (fun x ({ last } as entry) -> 
       let v = match last with | None -> Vbot | Some(v) -> v in
       { entry with last = None; cur = Some(v) }) acc_env

(* append [as_env] to [env] *)
let append_as_env as_env env =
  Env.append (Env.map (fun (_, entry) -> entry) as_env) env

(* update [acc_env] from [local_env] and [as_env] *)
(* every entry [x\{ cur = bot; last = v }] from [acc_env] for which [x\xi] *)
(* is in [as_env] and [xi\{ cur = vi }] is in [local_env] becomes *)
(* [x\{ cur = bot; last = \j:[i+1].if j = i then vi else v }] *)
let update_as_env loc i local_env as_env =
  let as_env =
    Env.mapi
      (fun x (xi, ({ last } as entry)) ->
        let entry =
          try
            let vi = Find.find_value_opt xi local_env in
            match vi, last with
            | Some(Value(vi)), Some(Value(Varray(v))) ->
               { entry with last = Some(Value(Varray(Arrays.extend loc vi v))) }
            | _ -> entry
          with
          | Not_found -> entry in
      (xi, entry))
      as_env in
  as_env

(* initialize from [as_env] with empty arrays *)
let initialize_as_env_with_empty_arrays as_env =
  let as_env =
    Env.fold
      (fun x xi acc ->
        Env.add x (xi, { cur = None; last = Some(Value(Arrays.empty));
                         default = None; reinit = false }) acc)
      as_env Env.empty in
  as_env

(* given [x] and [env_list], returns array [v] st [v.(i) = env_list.(i).(x)] *)
(* when [nb_of_missing_iterations <> 0] complete with a default element *)
let array_of
      nb_of_missing_iterations loc (var_name, var_init, var_default)
      acc_env env_list =
  let* v_list =
    map
      (fun env ->
        find_value_opt var_name env |>
          Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc })
      env_list in
  (* if one is bot or nil, the result is bot or nil *)
  let v_list = Primitives.slist v_list in
  if nb_of_missing_iterations = 0 then
    return (Primitives.lift (fun v -> Varray(Vflat(Array.of_list v))) v_list)
  else
    let* default =
      match var_init, var_default with
      | None, None ->
         let size = List.length env_list + nb_of_missing_iterations in
         error { kind = Earray_cannot_be_filled { name = var_name;
                                                  size = size;
                                                  nb_of_missing_iterations };
                 loc }
      | _, Some _ ->
         find_default_opt var_name acc_env |>
           Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc }
      | Some _, None ->
         find_last_opt var_name acc_env |>
           Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc } in
    match default with
    | Vbot -> return Vbot
    | Vnil -> return Vnil
    | Value(d) ->
       let d_list = Util.list_of nb_of_missing_iterations d in
       return (Primitives.lift
                 (fun v -> Varray(Vflat(Array.of_list (v @ d_list)))) v_list)

(* check that [v] is indeed an array of length [for_size] *)
let input loc v by =
  let+ v = v in
  match v with
  | Varray(a) ->
     let actual_size = Primitives.length a in
     return (Value(actual_size, Vinput { ve = a; by }))
  | _ -> error { kind = typ_error_array; loc }

let index loc ve_left ve_right dir =
  let+ ve_left = ve_left and+ ve_right = ve_right in
  match ve_left, ve_right with
  | Vint(ve_left), Vint(ve_right) ->
     let actual_size =
       (if dir then ve_right - ve_left else ve_left - ve_right) + 1 in
     return (Value(actual_size, Vindex { ve_left; ve_right; dir }))
  | _ -> error { kind = typ_error_array; loc }


(* loop iteration *)
(* parallel for loops; take a list of states *)
let foreach_i f s_list =
  let rec for_rec i s_list =
    match s_list with
    | [] -> return ([], [])
    | s :: s_list ->
       let* x, s = f i s in
       let* x_list, s_list = for_rec (i+1) s_list in
       return (x :: x_list, s :: s_list) in
  for_rec 0 s_list

(* instantaneous for loop; take a single state and iterate on it *)
let forward_i n default f s =
  let rec for_rec default i s =
    if i = n then return (default, s)
    else
      let* v, s = f i s in
      for_rec v (i+1) s in
  for_rec default 0 s

(* main entry functions *)

(* parallel loop: the step function is iterated with different states;
 *- output is an array. *)
let foreach_exp loc sbody env i_env s_list =
  let* ve_list, s_list =
    foreach_i
      (fun i se ->
        let* env_0 = geti_env loc i_env i in
        let env = Env.append env_0 env in
        sbody env se) s_list in
  let ve_list = Primitives.slist ve_list in
  return
    (Primitives.lift (fun v -> Varray(Vflat(Array.of_list v))) ve_list, s_list)

(* hyperserial loop: the step function is iterated on the very same state;
 *- output is the last value *)
let forward_exp loc sbody env i_env n default s =
  forward_i n default
      (fun i se ->
        let* env_0 = geti_env loc i_env i in
        let env = Env.append env_0 env in
        sbody env se) s

(* One step of the evaluation of the body of a loop *)
let step loc sbody env i_env i (acc_env, as_env) s =
  Debug.print_state "For loop: state before step = " s;
  (* take the projection on index [i] of the input environment [i_env] *)
  let* env_0 = geti_env loc i_env i in
  let env = Env.append env_0 env in
  Debug.print_ienv "For loop: acc_env = " acc_env;
  (* add [o\...] for every [o] declared [... as o] in the returns *)
  let env = append_as_env as_env env in
  let* is_exit, local_env, s = sbody env acc_env s in
  (* every entry [x\v] from [acc_env] becomes [x\{ cur = bot; last = v }] *)
  let acc_env = x_to_lastx acc_env local_env in
  (* every entry [x\{ cur = bot; last = v }] from [acc_env] for which [x\xi] *)
  (* is in [as_env] and [xi\{ cur = vi }] is in [local_env] becomes *)
  (* [x\{ cur = bot; last = \j:[i+1].if j = i then vi else v }] *)
  let as_env = update_as_env loc i local_env as_env in
  Debug.print_ienv "For loop: local_env = " local_env;
  Debug.print_ienv "For loop: acc_env = " acc_env;
  Debug.print_state "For loop: state after step = " s;
  return (is_exit, local_env, (acc_env, as_env), s)

(* The parallel for loop: it takes a list of [n] independent states, *)
(* a step function, an accumulated environment; returns both a list of *)
(* environments and a new accumulated environment. *)
(* The [foreach] corresponds to the mapfold with [n] distinct states *)
let foreach_eq f acc s_list = 
  let rec for_rec i acc s_list =
    match s_list with
    | [] -> return ([], acc, [])
    | s :: s_list ->
       let* f_env, acc, s = f i acc s in
       let* f_env_list, acc, s_list = for_rec (i+1) acc s_list in
       return (f_env :: f_env_list, acc, s :: s_list) in
  for_rec 0 acc s_list

(* The hyper-serial forward loop: it takes a state, a step function, *)
(* an accumulated environment; returns a list of *)
(* environments, a new accumulated environment and new state. *)
(* The [forward] corresponds to a mapfold with a single state *)
let forward_eq n f acc s =
  let rec for_rec i acc s =
    if i = n then return ([], acc, s)
    else begin
      let* is_exit, f_env, acc, s = f i acc s in
      if is_exit then
        return ([f_env], acc, s)
      else
        let* env_list, acc, s = for_rec (i+1) acc s in
        return (f_env :: env_list, acc, s)
      end in
  for_rec 0 acc s

(* The main entries *)
let foreach_eq loc sbody env i_env acc_env as_env s_list =
  let step_i i (acc_env, as_env) s =
    let* _, local_env, (acc_env, as_env), s =
      step loc sbody env i_env i (acc_env, as_env) s in
    return (local_env, (acc_env, as_env), s) in
  let as_env =
    initialize_as_env_with_empty_arrays as_env in
  let* env_list, (acc_env, as_env), s =
    foreach_eq step_i (acc_env, as_env) s_list in
  return (env_list, acc_env, s)

let forward_eq loc sbody env i_env acc_env as_env n s =
  let step_i i (acc_env, as_env) s =
    step loc sbody env i_env i (acc_env, as_env) s in
  let as_env =
    initialize_as_env_with_empty_arrays as_env in
  let* env_list, (acc_env, as_env), s =
    forward_eq n step_i (acc_env, as_env) s in
  return (env_list, acc_env, s)

