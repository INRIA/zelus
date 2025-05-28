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

(* Remove last in patterns; remove init and defaults in inputs/outputs *)
(* All variables in patterns must be values only                       *)
(* e.g., variables in function parameters, variables in pattern matchings *)
(* Any expression [last x] in an equation [eq] where [x] is expected to *)
(* be a value is rewritten [last* x] and [eq] replaced by *)
(* [local m do m = x and eq] *)

(* Example:
 *- [let node f(x) = ... x ... last x...] is rewritten
 *- [let node f(m) = local last x do x = m and ...m...last* x...]

 *- [let node f(...x init e1 default e0...) returns (...) ...x...last x]
 *- is rewritten
 *- [let node f(...m...) returns (...)
 *-       local x init ... default ... do x = m and ...m...last* x done]

 *- [let node f(...) returns (...x init ... default ...) ...x...last* x ...]
 *- is rewritten
 *- [let node f(...) returns (...m ...)
       local x init ... default ... do x = m and ...m...last* x]

 *- [match e with P(...x...) -> ...x...last x...] is rewritten
 *- [match e with P(...m...) -> local x do x = m and ...m...last* x...]
 *- [present
       e(...x...) -> ...x...last x...] is rewritten
 *- [present
       e(...m...) -> local x do x = m and ...m...last* m...]
 *)

           
open Zelus
open Ident

(* The accumulator is a map : [name -> name]. It associates a fresh *)
(* name [m] to every variable [x] for which [last x] is used *)
type acc = Ident.t Env.t

let empty = Env.empty

let build funs acc l_env =
  (* if [last x] is used, introduce a fresh name [m] and replace *)
  (* the declaration for [x] by a declaration for [m]. [x] is renamed [m] *)
  (* [last x], if it exists, is rewritten into [last* x] *)
  (* a local declaration is added that defines the variable [x] *)
  let add x ({ Deftypes.t_sort } as entry) (l_env, acc) =
    match t_sort with
    | Sort_mem { m_last = true } ->
       let m = fresh "m" in
       Env.add m { entry with t_sort = Sort_val } l_env, Env.add x m acc
    | _ -> Env.add x entry l_env, acc in
  Env.fold add l_env (Env.empty, acc)

let new_vardec v =
  { v with var_default = None; var_init = None;
           var_clock = false; var_typeconstraint = None;
           var_is_last = false; var_init_in_eq = false }

(* update a variable declaration; remove the initialization *)
(* and default part *)
let update_vardec acc (v_list, eq_list)
      ({ var_name; var_init; var_default; var_is_last; var_init_in_eq  } as v) =
  try
    let m = Env.find var_name acc in
    { (new_vardec v) with var_name = m },
    (v :: v_list, Aux.id_eq var_name (Aux.var m) :: eq_list)
  with
  | Not_found ->
     if (Util.is_opt var_init) || (Util.is_opt var_default) then
       let m = fresh "m" in
       { (new_vardec v) with var_name = m },
       (v :: v_list, eq_list)
     else v, (v_list, eq_list)

let var_ident funs acc x =
  try
    let m = Env.find x acc in m, acc
  with
  | Not_found -> x, acc

(* when [last x] appears, it is replaced by [last* x] *)
let last_ident funs acc ({ copy; id } as l) =
  try
    let _ = Env.find id acc in { l with copy = false }, acc
  with
  | Not_found -> l, acc

(* if [acc(x) = m] add the equation [x = m] to [eq_list] *)
let add_x_m acc x _ (v_list, eq_list) =
  try
    let m = Env.find x acc in
    Aux.vardec x false None None :: v_list,
    Aux.id_eq x (Aux.var m) :: eq_list
  with
  | Not_found -> v_list, eq_list

let add_equations_into_eq acc env eq =
  let v_list, eq_list = Env.fold (add_x_m acc) env ([], []) in
  Aux.eq_local_vardec v_list (eq :: eq_list)

let add_equations_into_e acc env e =
  let v_list, eq_list = Env.fold (add_x_m acc) env ([], []) in
  Aux.e_local_vardec v_list eq_list e

let match_handler_eq funs acc m_h =
  let ({ m_body; m_env } as m_h), acc_h =
    Mapfold.match_handler_eq funs acc m_h in
  (* add extra equations in the body *)
  { m_h with m_body = add_equations_into_eq acc_h m_env m_body }, acc

let match_handler_e funs acc m_h =
  let ({ m_body; m_env } as m_h), acc_h =
    Mapfold.match_handler_e funs acc m_h in
  (* add extra equations in the body *)
  { m_h with m_body = add_equations_into_e acc_h m_env m_body }, acc

let present_handler_eq funs acc p_b =
  let ({ p_body; p_env } as p_h), acc_h =
    Mapfold.present_handler_eq funs acc p_b in
  (* add extra equations in the body *)
  { p_h with p_body = add_equations_into_eq acc_h p_env p_body }, acc

let present_handler_e funs acc p_b =
  let ({ p_body; p_env } as p_h), acc_h =
    Mapfold.present_handler_e funs acc p_b in
  (* add extra equations in the body *)
  { p_h with p_body = add_equations_into_e acc_h p_env p_body }, acc

let for_returns funs acc ({ r_returns; r_block } as r) =
  let r_returns, acc =
    Util.mapfold (Mapfold.for_vardec_it funs) acc r_returns in
  let r_block, acc = Mapfold.block_it funs acc r_block in
  { r with r_returns; r_block }, acc

let for_eq_t funs acc ({ for_out; for_block } as f) =
  let for_out, acc =
    Util.mapfold (Mapfold.for_out_it funs) acc for_out in
  let for_block, acc = Mapfold.block_it funs acc for_block in
  { f with for_out; for_block }, acc

(* variables in blocks are unchanged *)
let block funs acc ({ b_vars; b_body; b_write } as b) =
  let b_vars, acc = 
    Util.mapfold (Mapfold.vardec_it funs) acc b_vars in
  let b_body, acc = Mapfold.equation_it funs acc b_body in
  { b with b_vars; b_body }, acc

let funexp funs acc ({ f_args; f_body = ({ r_desc } as r); f_env } as f) =
  let arg acc v_list = Util.mapfold (Mapfold.vardec_it funs) acc v_list in
  
  let f_args, acc = Util.mapfold arg acc f_args in
  let f_env, acc = Mapfold.build_it funs.global_funs acc f_env in
  
  let f_args, (v_list, eq_list) =
         Util.mapfold (Util.mapfold (update_vardec acc)) ([], []) f_args in
  let f_args, r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc = Mapfold.expression funs acc e in
       let e = Aux.e_local_vardec v_list eq_list e in
       f_args, Exp(e), acc
    | Returns (b) ->
       let { b_body } as b, acc = Mapfold.block_it funs acc b in
       let b_body = Aux.eq_local_vardec v_list (b_body :: eq_list) in
       f_args, Returns { b with b_body }, acc in
  { f with f_args; f_body = { r with r_desc }; f_env }, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs =
    { Mapfold.default_global_funs with build; var_ident; last_ident }  in
  let funs = 
    { Mapfold.defaults with match_handler_eq; match_handler_e;
                            present_handler_eq; present_handler_e;
                            for_returns; for_eq_t; block; funexp;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
 
