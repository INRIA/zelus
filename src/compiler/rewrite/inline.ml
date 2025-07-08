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

(* Inlining of function calls. Only global function names are inlined *)

open Misc
open Location
open Ident
open Zelus
open Mapfold

exception Cannot_inline

let _ = inlining_level := -100000

(* a value is a closure: inline fun x1... -> e paired with an environment *)
type value =
  { f_args: Typinfo.arg list; f_body: Typinfo.result;
    f_env: Typinfo.ienv Env.t; f_acc: acc }
    
and acc =
  { renaming: Ident.t Env.t; (* renaming *)
    subst: value Env.t; (* substitution *)
  }

let empty = { renaming = Env.empty; subst = Env.empty }

let eq_empty = Aux.eqmake Defnames.empty EQempty
    
let fresh () = Ident.fresh "inline"

let rec is_a_value { e_desc } =
  match e_desc with
  | Evar _ | Eglobal _ | Econst _ | Efun _ -> true
  | Etuple(e_list) -> List.for_all is_a_value e_list
  | Erecord(l_e_list) ->
     List.for_all (fun { arg } -> is_a_value arg) l_e_list
  | _ -> false

let make_equation ({ subst } as acc) x { e_desc } =
  match e_desc with
    Efun({ f_inline = true; f_args; f_body; f_env }) ->
     { acc with subst = Env.add x { f_args; f_body; f_env; f_acc = acc } subst }
  | Evar(y) ->
     let acc = 
       try { acc with subst = Env.add x (Env.find y subst) subst }
       with Not_found -> acc in
     acc
  | _ -> raise Cannot_inline

(* given [f_arg1;...;f_arg_n] and [arg1;...;arg_n] *)
(* define [f_arg1 = arg1;...; f_arg_n = arg_n] *)
(* if [arg_i] is a value, the pair [f_arg_i = arg_i] is added to [subst] *)
let match_f_arg_with_arg acc f_args arg_list =
  let match_t (acc, eq_list) f_arg arg =
    try
      match f_arg, arg with
      | [{ var_name = x }], e -> make_equation acc x e, eq_list
      | _ -> raise Cannot_inline
    with
    | Cannot_inline ->
        let eq_list = Aux.match_f_arg_with_arg f_arg arg :: eq_list in
        acc, eq_list in
  List.fold_left2 match_t (acc, []) f_args arg_list

(* Main Transformation *)
(* [(\a1...an. e) e1 ... en] 
 *- rewrites to:
 *- [local a1',...,an' do a1' = e1 ... an' = en in r[ai\ai']]
 *- [(\(a1 ... an returns p eq) e1 ... en
 *- rewrites to:
 *- [local a1',...,an', v_ret'
 *-  do a1' = e1 ... an' = en and eq[ai\ai'] in v_ret' *)
 let local_in funs f_acc f_args arg_list f_env r =
   (* recursively treat the argument *)
   let arg acc v_list =
     Util.mapfold (Mapfold.vardec_it funs) acc v_list in

   (* build a renaming for the arguments *)
   let f_env, acc = Mapfold.build_it funs.global_funs f_acc f_env in
   (* rename the list of arguments *)
   let f_args, acc = Util.mapfold arg acc f_args in  
     
   (* build a list of equations *)
   let acc, eq_list = match_f_arg_with_arg f_acc f_args arg_list in

   (* flatten the list of arguments *)
   let vardec_list = List.flatten f_args in
   
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

(* application *)
let apply funs ({ subst } as acc) { e_desc } arg_list =
  match e_desc with
  | Evar(x) ->
     let e, acc =
       try
         let { f_args; f_body; f_env; f_acc } = Env.find x subst in
         local_in funs f_acc f_args arg_list f_env f_body
       with
       | Not_found -> raise Cannot_inline in
     e, acc
  | Efun({ f_inline = true; f_args; f_body; f_env }) ->
     local_in funs acc f_args arg_list f_env f_body
  | _ -> raise Cannot_inline

(* Build a renaming from an environment *)
let build global_funs ({ renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }

let var_ident global_funs ({ renaming } as acc) x =
 Env.find_stop_if_unbound "Error in pass Inline" x renaming, acc

(* expressions *)
let expression funs ({ renaming; subst } as acc) ({ e_desc } as e) = 
  match e_desc with
  | Eapp({ f; arg_list } as app) ->
     let f, acc = Mapfold.expression_it funs acc f in
     let arg_list, acc =
       Util.mapfold (Mapfold.expression_it funs) acc arg_list in
     let e, acc =
       try
         apply funs acc f arg_list
       with
         Cannot_inline ->
         { e with e_desc = Eapp({ app with f; arg_list }) }, acc in
     e, acc
  | _ -> raise Mapfold.Fallback

let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQeq({ pat_desc = Evarpat(x) } as p, e) ->
     let x, acc = Mapfold.var_ident_it funs.global_funs acc x in
     let e, acc = Mapfold.expression_it funs acc e in
     let eq, acc =
       try
         let acc = make_equation acc x e in eq_empty, acc
       with Cannot_inline -> { eq with eq_desc = EQeq(p, e) }, acc in
     eq, acc
  | _ -> raise Mapfold.Fallback

(* all local names can restart from 0 *)
(* to be done later; for the moment, starts from the current value *)
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with
      global_funs; expression; equation; set_index; get_index; } in
  let p, _ = Mapfold.program_it funs empty p in
  p




    (*
      let expression funs ({ renaming; subst } as acc) ({ e_desc } as e) = 
  match e_desc with
  | Evar(x) ->
     (* let l_ = Env.to_list renaming in
     let l__ = Env.to_list subst in *)
     let e =
       try
         Env.find x subst
       with
         Not_found ->
           let m = Env.find x renaming in { e with e_desc = Evar(m) } in
     e, acc
  | Eapp({ f; arg_list } as app) ->
     let f, acc = Mapfold.expression_it funs acc f in
     let arg_list, acc =
       Util.mapfold (Mapfold.expression_it funs) acc arg_list in
     let e, acc =
       try apply funs acc f arg_list
       with Cannot_inline ->
         { e with e_desc = Eapp({ app with f; arg_list }) }, acc in
     e, acc
  | _ -> raise Mapfold.Fallback

let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQeq({ pat_desc = Evarpat(x) } as p, e) ->
     let e, acc = Mapfold.expression_it funs acc e in
     let eq, acc =
       try
         let acc = make_equation acc x e in eq_empty, acc
       with Cannot_inline -> { eq with eq_desc = EQeq(p, e) }, acc in
     eq, acc
  | _ -> raise Mapfold.Fallback
     *)




(*
(* the type of the accumulator *)
type 'a acc =
  { (* the global environment *)
    genv : 'a Genv.genv;
    (* the renaming environment; all names must be renamed to ensure *)
    (* that the same name is never defined twice in a file *)
    renaming : Ident.t Env.t;
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

let var_ident global_funs ({ renaming } as acc) x =
 Env.find_stop_if_unbound "Error in pass Inline" x renaming, acc

(* Main transformation *)
(* [(\a1...an. e) e1 ... en] 
 *- rewrites to:
 *- [local a1',...,an' do a1' = e1 ... an' = en in r[ai\ai']]
 *- [(\(a1 ... an returns p eq) e1 ... en
 *- rewrites to:
 *- [local a1',...,an', v_ret'
 *-  do a1' = e1 ... an' = en and eq[ai\ai'] in v_ret' *)
let local_in funs f_env f_args arg_list acc r =
  (* rename an argument *)
  let arg acc v_list =
    Util.mapfold (Mapfold.vardec_it funs) acc v_list in
  (* build a renaming for arguments *)
  let f_env, acc = Mapfold.build_it funs.global_funs acc f_env in
  (* rename the list of arguments *)
  let f_args, acc = Util.mapfold arg acc f_args in  

  (* build a list of equations *)
  let eq_list = List.map2 Aux.match_f_arg_with_arg f_args arg_list in

  (* flatten the list of arguments *)
  let vardec_list = List.flatten f_args in

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
let expression funs ({ genv; renaming } as acc) e = 
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
  | Eapp _ ->
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

 *)
