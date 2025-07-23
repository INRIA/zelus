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

(* Specialization of recursive size functions *)

(* declarations [let rec f1<<n1,...>> = ... and fk<<<n1,...>> = ...] *)
(* are removed. Fresh functions are introduced for all specialized applications *)
(* that is, f<<s1,...>> where [s1,...] is a list of constant values *)

open Misc
open Location
open Ident
open Zelus

(* memoization table; mapping [id(s1,...,sn) -> id_j] *)
module Memo = 
  Map.Make 
    (struct 
      type t = int list 
      let compare = Stdlib.compare
    end)

type acc =
  { (* a map [f_v -> e] where [f_v] is the name of a specialized size function app. *)
    env_of_sizefun: sizefun_entry Env.t;
    (* map of size functions [f -> <<n1,...>>.e] *)
    env_of_sizes: int Env.t;
  (* map of sizes [id -> v] with [v] a (positive) integer *)
  }

and sizefun_entry =
  { sizefun: Typinfo.sizefun;
      (* size function: [sf_id <<n1,...>> = e] *)
    mutable sizefun_specialized: (Ident.t * Typinfo.exp) list;
      (* the list of specialized functions created for [sf_id] *)
    sizefun_memo_table: Ident.t Memo.t;
      (* the memoization table which associate a fresh name [id] to <<s1,...,sn>> *)
    mutable used: bool;
      (* is [sf_id] used or not in the code *)
  }

let empty = 
  { env_of_sizefun = Env.empty; env_of_sizes = Env.empty }

let add_sizefun ({ env_of_sizefun } as acc) ({ sf_id } as sizefun) =
  { acc with env_of_sizefun =
               Env.add sf_id { sizefun; used = false;
                               sizefun_specialized = [];
                               sizefun_memo_table = Memo.empty }
                 env_of_sizefun  }

let find_sizefun sf_id { env_of_sizefun } =
  try
    Env.find sf_id env_of_sizefun
  with
    Not_found -> assert false

let is_used sf_id env_of_sizefun =
  let { used } = find_sizefun sf_id env_of_sizefun in used

let set_used sf_id { env_of_sizefun } =
  try
    let { used } as entry = Env.find sf_id env_of_sizefun in
    entry.used <- true
  with
    Not_found -> ()

let add_sizefun_specialized sf_id (sf_fresh_id, e) acc =
  let { sizefun_specialized } as entry = find_sizefun sf_id acc in
  entry.sizefun_specialized <- (sf_fresh_id, e) :: sizefun_specialized;
  acc

let size env_of_sizes s =
  let rec size { desc } =
    match desc with
    | Size_int(i) -> i
    | Size_var(id) -> Env.find id env_of_sizes
    | Size_frac { num; denom } -> size num / denom
    | Size_op(op, s1, s2) ->
       let v1 = size s1 and v2 = size s2 in
       match op with
       | Size_plus -> v1 + v2 | Size_minus -> v1 - v2 | Size_mult -> v1 * v2 in
  try
    size s
  with
    Not_found -> assert false

(* A generic operator to three [let leq in e] and [let leq in eq] *)
let let_in funs body_it acc ({ l_eq; l_loc } as leq) b =
  match Typing.eq_or_sizefun l_loc l_eq with
  | Either.Left _ ->
     let leq, acc = Mapfold.leq_it funs acc leq in
     let b, acc = body_it funs acc b in
     (Some leq, b), acc
  | Either.Right(sizefun_list) ->
     (* add entry [sf_id -> sizefun] for every element of the list *)
     let sf_id_list, acc =
       List.fold_left
         (fun (sf_id_list, acc) ({ sf_id } as sizefun) ->
           sf_id :: sf_id_list, add_sizefun acc sizefun)
         ([], acc) sizefun_list in
     (* if one use of [sf_id] remains the size function definitions are kept *)
     let used =
       List.fold_left
         (fun used sf_id ->
           used || (is_used sf_id acc)) false sf_id_list in
     let b, acc = body_it funs acc b in
     if used then
       (* keep the list of size function definitions *)
       (Some leq, b), acc
     else
       (* remove them *)
       (None, b), acc

let equation funs acc ({ eq_desc; eq_loc } as eq) =
  match eq_desc with
  | EQlet({ l_eq } as leq, eq_let) ->
     let (leq_opt, eq_let), acc =
       let_in funs Mapfold.equation_it acc leq eq_let in
     { eq with eq_desc = Aux.opt_eq_let_desc leq_opt eq_let }, acc
  | _ -> raise Mapfold.Fallback

(* add a new function definition [sf_id = sf_e[v1/id1,...,vn/idn]] *)
let add_new_fun funs ({ env_of_sizes } as acc) (sf_id, sf_id_list, v_list, sf_e) =
  let sf_fresh_id = fresh (Ident.name sf_id) in
  let env_of_sizes =
    List.fold_left2
      (fun env_of_sizes sf_id v -> Env.add sf_id v env_of_sizes)
      env_of_sizes sf_id_list v_list in
  let sf_e, acc = Mapfold.expression_it funs { acc with env_of_sizes } sf_e in
  (* add the new function to the list of specialized size functions for [sf_id] *)
  let acc = add_sizefun_specialized sf_id (sf_fresh_id, sf_e) acc in
  sf_fresh_id, acc
     
let expression funs ({ env_of_sizefun; env_of_sizes } as acc) 
      ({ e_desc; e_loc } as e) =
  match e_desc with
  | Evar(x) ->
     (* the variable [x] is used *)
     set_used x acc; e, acc     
  | Elet({ l_eq } as leq, e_let) ->
     let (leq_opt, e_let), acc =
       let_in funs Mapfold.expression_it acc leq e_let in
     { e with e_desc = Aux.opt_e_let_desc leq_opt e_let }, acc
  | Esizeapp { f = { e_desc = Evar(f) }; size_list } ->
     (* [f <<s1,...>>] where the [s_i] are immediate values] *)
     begin try
         let { sizefun = { sf_id; sf_id_list; sf_e; sf_loc; sf_env };
               sizefun_memo_table } as f =
          Env.find f env_of_sizefun in
        let v_list = List.map (size env_of_sizes) size_list in
        let id, acc =
          try
            Memo.find v_list sizefun_memo_table, acc
          with
            Not_found ->
              add_new_fun funs acc (sf_id, sf_id_list, v_list, sf_e) in
        { e with e_desc = Evar(id) }, acc
       with
         Not_found -> e, acc
     end
  | _ -> raise Mapfold.Fallback

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with
      global_funs; equation; expression; set_index; get_index; } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list } 
