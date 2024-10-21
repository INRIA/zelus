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

(* Remove last in patterns; remove init and defaults in inputs/outputs *)
(* All variables in patterns must be values only                          *)
(* e.g., function parameters, patterns in pattern matching handlers, etc. *)
(* Any expression [last x] in an equation [eq] where [x] is expected to *)
(* be a value is rewritten [last* x] and [eq] replaced by *)
(* [local m do m = x and eq] *)

(* Example:
 *- [let node f(x) = ... last x...] is rewritten
 *- [let node f(m) = local x do x = m and ... last* x...]

 *- [let node f(...x init e1 default e0...) returns (...) ...last x] is rewritten
 *- [let node f(...m...) returns (...)
 *-       local x init ... default ... do x = m and ...last* x done]

 *- [let node f(...) returns (...x init ... default ...) ... last x ...] is rewritten
 *- [let node f(...) returns (...m ...)
       local x init ... default ... do m = x and ... last* x]

 *- [match e with P(...x...) -> eq] is rewritten
 *- [match e with P(...m...) -> 
       local x do x = m and eq[last* x \ last x]]
 *- [present
       e(...x...) -> eq...[last x]...] is rewritten
 *- [present
       e(...m...) ->
         local x do x = m and eq[last* x \ last x]]
 *)

           
open Zelus
open Ident

type acc = entry Env.t

and entry = { last_is_used: bool; new_name: Ident.t }

let empty = Env.empty

let new_vardec v =
  { v with var_default = None; var_init = None;
           var_clock = false; var_typeconstraint = None;
           var_is_last = false; var_init_in_eq = false }

let update_vardec acc ({ var_name } as v) =
  try
    let { new_name } = Env.find var_name acc in
    { (new_vardec v) with var_name = new_name }
  with
    | Not_found -> v

let build funs acc l_env =
  let add x entry (new_env, acc) =
    let m = fresh "m" in
    Env.add m entry new_env,
    Env.add x { last_is_used = false; new_name = m } acc in
  Env.fold add l_env (Env.empty, acc)

let var_ident funs acc x =
  try
    let { new_name } = Env.find x acc in new_name, acc
  with
  | Not_found -> x, acc

(* when [last x] appears, it is replaced by [last* x] and [x] is marked to *)
(* be used in [acc] *)
let last_ident funs acc ({ copy; id } as l) =
  try
    let { last_is_used; new_name } = Env.find id acc in
    let acc = if last_is_used then acc
              else
                Env.update id
                  (function | None -> None
                            | Some(z) -> Some { z with last_is_used = true })
                  acc in
    { l with copy = false }, acc
  with
  | Not_found -> l, acc

(* if [acc(x) = { last_is_used; new_name = m }] add equation [x = m] *)
let add acc x _ (v_list, eq_list) =
  try
    let { last_is_used; new_name } = Env.find x acc in
    if last_is_used then
      Aux.vardec x false None None :: v_list,
      Aux.id_eq x (Aux.var new_name) :: eq_list
    else v_list, eq_list
  with
  | Not_found -> v_list, eq_list

let add_equations_into_eq acc env eq =
  let v_list, eq_list = Env.fold (add acc) env ([], []) in
  Aux.eq_local_vardec v_list (eq :: eq_list)

let add_equations_into_e acc env e =
  let v_list, eq_list = Env.fold (add acc) env ([], []) in
  Aux.e_local_vardec v_list eq_list e

let match_handler_eq funs acc m_h =
  let ({ m_body; m_env } as m_h), acc_h = Mapfold.match_handler_eq funs acc m_h in
  (* add extra equations in the body *)
  { m_h with m_body = add_equations_into_eq acc_h m_env m_body }, acc

let match_handler_e funs acc m_h =
  let ({ m_body; m_env } as m_h), acc_h = Mapfold.match_handler_e funs acc m_h in
  (* add extra equations in the body *)
  { m_h with m_body = add_equations_into_e acc_h m_env m_body }, acc

let present_handler_eq funs acc p_b =
  let ({ p_body; p_env } as p_h), acc_h = Mapfold.present_handler_eq funs acc p_b in
  (* add extra equations in the body *)
  { p_h with p_body = add_equations_into_eq acc_h p_env p_body }, acc

let present_handler_e funs acc p_b =
  let ({ p_body; p_env } as p_h), acc_h = Mapfold.present_handler_e funs acc p_b in
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

let update_arg_list acc (v_list, eq_list) f_args =
  let update_vardec acc (v_list, eq_list)
        ({ var_name; var_init; var_default; var_is_last; var_init_in_eq } as v) =
    let is_none = function | None -> true | _ -> false in
    let i = (is_none var_init) && (is_none var_default)
            && not var_is_last && not var_init_in_eq in
    let { last_is_used; new_name } =
      try Env.find var_name acc with | Not_found -> assert false in
    { (new_vardec v) with var_name = new_name },
    if last_is_used || not i then
      v :: v_list, Aux.id_eq var_name (Aux.var new_name) :: eq_list
    else v_list, eq_list in

  Util.mapfold (fun (v_list, eq_list) arg ->
      Util.mapfold (update_vardec acc) (v_list, eq_list) arg) ([], []) f_args

let funexp funs acc ({ f_args; f_body = ({ r_desc } as r); f_env } as f) =
  let arg acc v_list = Util.mapfold (Mapfold.vardec_it funs) acc v_list in
  let f_args, acc = Util.mapfold arg acc f_args in

  let f_env, acc = Mapfold.build_it funs.global_funs acc f_env in

  let f_args, r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc = Mapfold.expression funs acc e in
       let f_args, (v_list, eq_list) = update_arg_list acc ([], []) f_args in
       let e = Aux.e_local_vardec v_list eq_list e in
       f_args, Exp(e), acc
    | Returns (b) ->
       let { b_body } as b, acc = Mapfold.block_it funs acc b in
       let f_args, (v_list, eq_list) = update_arg_list acc ([], []) f_args in
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
 
