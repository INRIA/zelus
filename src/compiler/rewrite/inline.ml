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

(* Inlining of function calls. Only global function names are inlined *)
(* - function calls annotated with [inline] are systematically inlined *)
(* - small functions (according to a cost function) are statically expanded *)

open Misc
open Location
open Zelus
open Ident
open Lident
open Defnames
open Genv
open Value
open Error
open Mapfold

exception No_inline

let _ = inlining_level := -100000

(* the type of the accumulator *)
type 'a acc =
  { genv : 'a Genv.genv;
    (* the global environment *)
    renaming : Ident.t Env.t;
    (* name to name environment *)
  }

let empty = { genv = Genv.empty; renaming = Env.empty }

(* Inlining decision. The function call [lname e1 ... en] is inlined *)
(* either because [is_inline = true] or the body is small enough *)
let inline is_inline { genv } lname =
  let { Genv.info } = 
    try 
      (* temporary patch. 10/06/2025 *)
      if is_inline then Genv.find_value lname genv else raise Not_found
    with
      Not_found ->
      if is_inline then
        Format.eprintf 
          "Inline error: unbound global %s at function call\n" 
          (Lident.modname lname);
      raise No_inline in
  match info with
  | Vclosure({ c_funexp = { f_args; f_body; f_env }; c_genv } as closure) ->
     (* the local environment [c_env] should be empty *)
     if is_inline then closure
     else if Cost.result (!inlining_level + List.length f_args) f_body
     then closure else raise No_inline
  | _ -> raise No_inline

(* Build a renaming from an environment *)
let build global_funs ({ renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }

let intro_ident global_funs ({ renaming } as acc) n =
  let m = Ident.fresh (Ident.source n) in
  m, { acc with renaming = Env.add n m renaming }

let var_ident global_funs ({ renaming } as acc) x =
  try Env.find x renaming, acc with Not_found ->
    Format.eprintf 
      "Inline error: unbound local variable %s\n" (Ident.name x);
    raise Error

(* Main transformation *)
(* [(\a1...an. e) e1 ... en] 
 *- rewrites to:
 *- [local a1',...,an' do a1' = e1 ... an' = en in e[ai\ai']]
 *- [(\(a1 ... an. v_ret eq) e1 ... en
 *- rewrites to:
 *- [local a1',...,an', v_ret'
 *-  do a1' = e1 ... an' = en and eq[ai\ai'] in v_ret' *)
let local_in funs f_env f_args arg_list acc r =
  (* rename an argument *)
  let arg acc v_list =
    Util.mapfold (Mapfold.vardec_it funs) acc v_list in
  (* build a renaming for arguments *)
  let f_env, acc = build funs.global_funs acc f_env in
  (* rename the list of arguments *)
  let f_args, acc = Util.mapfold arg acc f_args in  
  (* build a list of equations *)
  let eq_list = List.map2 Aux.eq_of_f_arg_arg_make f_args arg_list in
  let vardec_list =
    List.fold_left (fun acc vardec_list -> vardec_list @ acc) [] f_args in
  let { r_desc } as r, acc = Mapfold.result_it funs acc r in
  match r_desc with
  | Exp(e_r) ->
     Aux.emake (Elocal(Aux.block_make vardec_list eq_list, e_r)), acc
  | Returns { b_vars; b_body } ->
     let vardec_list = b_vars @ vardec_list in
     let eq_list = b_body :: eq_list in
     Aux.emake
       (Elocal(Aux.block_make vardec_list eq_list,
               Aux.returns_of_vardec_list_make b_vars)), acc

(* Expressions *)
let expression funs ({ genv } as acc) e = 
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eapp { is_inline; f = { e_desc = Eglobal { lname } }; arg_list } ->
     let e, acc =
       try
         let { c_funexp = { f_args; f_body; f_env }; c_genv } =
           inline (is_inline || !Misc.inline_all) acc lname in
         local_in
           funs f_env f_args arg_list { acc with genv = c_genv } f_body
       with No_inline -> e, acc in
     e, acc
  | _ -> e, acc

let open_t funs ({ genv } as acc) modname =
  let genv = Genv.try_to_open_module genv modname in modname, { acc with genv }

(* all local names can restart from 0 *)
(* to be done later; for the moment, starts from the current value *)
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with
      expression; global_funs; set_index; get_index; open_t } in
  let p, _ = Mapfold.program_it funs { empty with genv } p in
  p

