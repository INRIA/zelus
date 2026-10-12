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

(* translate control expressions into equations *)
(* the constructs that are concerned are:
 *- by-case definition (pattern matching) [match e with ...]
 *- reset [reset e every c]
 *- present [...]
 *- foreach and forward
 *-
 *- by-case (total):
    [match e with P1 -> e1 | ... | Pn -> en] =>
    [let match e with P1 -> r = e1 | ... | Pn -> r = en in r]
    by-case (partial):
    [match e with P1 -> e1 | ... ] =>
    [let match e with P1 -> emit r = e1 | ... | Pn -> emit r = en in r]
*- [reset e every c] => let reset r = e every c in r]
*)

open Misc
open Location
open Ident
open Zelus
open Mapfold

let empty = ()

let fresh () = Ident.fresh "r"

let make_result_desc loc result desc =
  Aux.eq_location loc (Aux.eqmake (Defnames.singleton result) desc)

(* translate a by-case definition *)
let match_exp_to_eq e_loc acc (is_size, is_total, e, handlers) =
  let result = fresh () in
  (* when [not is_total], [result] is a signal *)
  let handler ({ m_body } as h) =
    let m_body = if is_total then Aux.id_eq result m_body
                 else Aux.emit_id_eq result m_body in
    { h with m_body } in
  let eq =
    make_result_desc e_loc result
      (EQmatch
         { is_size; is_total; e; handlers = List.map handler handlers }) in
  (* [let match e with (P_i -> r = e_i)_i in r] *)
  (* or [let match e with (P_i -> emit r = e_i)_i in r *)
  Aux.let_leq_in_e (Aux.leq false [eq]) (Aux.var result), acc

(* translate a reset *)
let reset_exp_to_eq e_loc acc (e, e_r) =
  let result = fresh () in
  let eq =
    make_result_desc e_loc result (EQreset(Aux.id_eq result e, e_r)) in      
  Aux.let_leq_in_e (Aux.leq false [eq]) (Aux.var result), acc

(* translate a present *)
let present_exp_to_eq e_loc acc (handlers, default_opt) =
  let result = fresh () in
  let handler ({ p_body } as h) =
    { h with p_body = Aux.id_eq result p_body } in
  let default desc =
    match desc with
    | Init(e) -> Init(Aux.id_eq result e)
    | Else(e) -> Else(Aux.id_eq result e)
    | NoDefault -> NoDefault in
  let eq =
    make_result_desc e_loc result
      (EQpresent { handlers = List.map handler handlers;
                   default_opt = default default_opt }) in
  Aux.let_leq_in_e (Aux.leq false [eq]) (Aux.var result), acc

(* translate a for loop *)
(*  [forward ... do e default e_d done] =>
         returns (result as result_l default e_d) result_l = e]
 *- [foreach ... do e default e_d done] =>
         returns (result_l default e_d out result as result_as) result_l = e]
 *- [returns ([|xi init ei default e'i |] ...) eq =>
       returns (result1_i init ei default e'i out result1,...)] *)
let for_exp_to_eq e_loc is_a_forward_loop acc
      (for_size, for_kind, for_index,
       for_input, for_let, for_body, for_resume, for_env) =
  let for_out_from_exp loc result result_l default =
    let for_out_vardec =
      { for_name = result_l; for_ty_cstr = None;
        for_init = None; for_default = default } in
    let for_locals =
      if is_a_forward_loop then
        OAcc { for_acc = for_out_vardec }
      else let result_as = fresh () in
           OArray { for_item = for_out_vardec; for_as = result_as } in
    { desc = { for_ext = result;
               for_locals; for_info = Typinfo.no_info }; loc = e_loc } in
  let for_out_from_returns { desc = { for_array; for_vardec; for_as } } =
    let result = fresh () in
    let for_out_vardec_t
          { var_loc; var_name; var_default; var_init; var_typeconstraint } =
      var_loc,
      { for_name = result; for_ty_cstr = var_typeconstraint;
        for_init = var_init; for_default = var_default } in
    let loc, for_out_vardec = for_out_vardec_t for_vardec in
    Aux.var result,
    { desc =
        { for_ext = result;
          for_locals =
            (if for_array < 1 then OAcc { for_acc = for_out_vardec }
             else
               let for_as =
                 match for_as with | None -> fresh () | Some(for_as) -> for_as in
               OArray { for_item = for_out_vardec; for_as });
          for_info = Typinfo.no_info };
      loc = loc } in

  let result, for_body =
    match for_body with
    | Forexp { exp; default } ->
       (* [...do (e default e_d)] *)
       let result = fresh () in
       let result_l = fresh () in
       (* rewrites to [...returns (result as result_l default e_d) result_l = e] *)
       let eq = Aux.id_eq result_l exp in
       Aux.var result,
       { for_eq_out = [for_out_from_exp exp.e_loc result result_l default];
         for_eq_block = Aux.block_make [] [eq];
         for_eq_env = Aux.env_of (S.singleton result_l) }
    | Forreturns { r_returns; r_block; r_env } ->
       (* [...returns ([|x init exi default fxi|],..., yi init eyi fyi,...)] *)
       let result_for_eq_out_list =
         List.map for_out_from_returns r_returns in
       let result_list, for_eq_out_list = List.split result_for_eq_out_list in
       Aux.tuple_or_single result_list,
       { for_eq_out = for_eq_out_list;
         for_eq_block  = r_block;
         for_eq_env = r_env } in
  let eq =
    Aux.eqmake (Defnames.empty)
      (EQforloop { for_size; for_kind; for_index;
                   for_input; for_let; for_body; for_resume; for_env }) in
  Aux.let_leq_in_e (Aux.leq false [eq]) result, acc
    
let expression funs acc e =
  let { e_desc; e_loc } as e, acc = Mapfold.expression funs acc e in 
  match e_desc with
  | Ematch { is_size; is_total; e; handlers } ->
     match_exp_to_eq e_loc acc (is_size, is_total, e, handlers)
  | Ereset(e, e_r) ->
     reset_exp_to_eq e_loc acc (e, e_r)
  | Epresent { handlers; default_opt } ->
     present_exp_to_eq e_loc acc (handlers, default_opt)
  | Eforloop  { for_size; for_kind; for_index;
                for_input; for_let; for_body; for_resume; for_env } ->
     let is_a_forward_loop = match for_kind with | Kforward _ -> true | _ -> false in
     for_exp_to_eq e_loc is_a_forward_loop acc
       (for_size, for_kind, for_index,
        for_input, for_let, for_body, for_resume, for_env)
  | _ -> e, acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

    
