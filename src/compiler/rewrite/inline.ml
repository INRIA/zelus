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

(* a value is a closure: <inline fun x1... -> e, acc> where [acc] *)
(* is a pair of environments; one for renaming variables; one for values *)
type value =
  { f_args: Typinfo.arg list; f_body: Typinfo.result;
    f_env: Typinfo.ienv Env.t; f_acc: acc }
    
and acc =
  { renaming: Ident.t Env.t; (* renaming *)
    subst: value Env.t; (* substitution *)
  }

let empty = { renaming = Env.empty; subst = Env.empty }

let eq_empty = Aux.eqmake Defnames.empty EQempty
    
let append { subst = s } ({ subst } as acc) = { acc with subst = Env.append subst s }

let fresh () = Ident.fresh "inline"

(* when [e] has value [v], add an entry [x\v] to [subst] *)
let make_subst ({ subst } as acc) x { e_desc } =
  match e_desc with
  | Evar(y) ->
     let acc = 
       try { acc with subst = Env.add x (Env.find y subst) subst }
       with Not_found -> acc in
     acc
  | _ -> raise Cannot_inline

let value { subst } { e_desc } =
  match e_desc with
  | Evar(y) ->
     let v = try Env.find y subst with Not_found -> raise Cannot_inline in v
  | _ -> raise Cannot_inline

(* given [f_arg1;...;f_arg_n] and [arg1;...;arg_n] *)
(* define [f_arg1 = arg1;...; f_arg_n = arg_n] *)
(* if [arg_i] is a value, the binding [f_arg_i\arg_i] is added to [subst] *)
(* [acc] is the current environment in which [e] is evaluated. [f_acc] *)
(* is the environment augmented with new bindings *)
let match_f_arg_with_arg acc f_acc (f_args, arg_list) =
  let match_t (eq_list, ({ subst } as f_acc)) f_arg arg =
    try
      match f_arg, arg with
      | [{ var_name = x }], e ->
         eq_list, { f_acc with subst = Env.add x (value acc e) subst }
      | _ -> raise Cannot_inline
    with
    | Cannot_inline ->
        let eq_list = (Aux.match_f_arg_with_arg f_arg arg) :: eq_list in
        eq_list, f_acc in
  List.fold_left2 match_t ([], f_acc) f_args arg_list

(* Main Transformation *)
(* [(\a1...an. e) e1 ... en] 
 *- rewrites to:
 *- [local a1',...,an' do a1' = e1 ... an' = en in r[ai\ai']]
 *- [(\(a1 ... an returns p eq) e1 ... en
 *- rewrites to:
 *- [local a1',...,an', v_ret'
 *-  do a1' = e1 ... an' = en and eq[ai\ai'] in v_ret' *)
 let local_in funs acc (f_args, arg_list, f_env, f_acc) result =
   (* recursively treat the argument *)
   let params f_acc v_list =
     Util.mapfold (Mapfold.vardec_it funs) f_acc v_list in

   (* build a renaming for the formal parameters *)
   let f_env, f_acc = Mapfold.build_it funs.global_funs f_acc f_env in
   (* rename the list of parameters *)
   let f_args, f_acc = Util.mapfold params f_acc f_args in  
     
   (* build a list of equations *)
   let eq_list, f_acc = match_f_arg_with_arg acc f_acc (f_args, arg_list) in

   (* flatten the list of arguments *)
   let vardec_list = List.flatten f_args in
   (* keeps those whose name [x] is not bound in [f_acc] *)
   let vardec_list =
     List.filter (fun { var_name } -> Env.mem var_name acc.subst) vardec_list in 

   (* inlining is done recursively on the body [f_body] *)
   let { r_desc } as r, f_acc = Mapfold.result_it funs f_acc result in
   let e = match r_desc with
     | Exp(e_r) ->
        Aux.e_local_vardec vardec_list eq_list e_r
     | Returns { b_vars; b_body } ->
        let vardec_list = b_vars @ vardec_list in
        let eq_list = b_body :: eq_list in
        Aux.e_local_vardec vardec_list eq_list
        (Aux.returns_of_vardec_list_make b_vars) in
   e, append f_acc acc

(* application *)
let rec apply funs ({ subst } as acc) { e_desc } arg_list =
  match e_desc with
  | Evar(x) ->
     let e, acc =
       try
         let { f_args; f_body; f_env; f_acc } = Env.find x subst in
         if List.length f_args = List.length arg_list
         then local_in funs acc (f_args, arg_list, f_env, f_acc) f_body
         else raise Cannot_inline
       with
       | Not_found -> raise Cannot_inline in
     e, acc
  | Eop((Erun _ | Eatomic), [e]) -> apply funs acc e arg_list
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
  | Efun({ f_inline = true; f_args; f_body; f_env }) ->
     let m = fresh () in
     { e with e_desc = Evar(m) },
     { acc with subst = Env.add m { f_args; f_body; f_env; f_acc = acc } subst }
  | Eapp({ f; arg_list } as app) ->
     let f, acc = Mapfold.expression_it funs acc f in
     let arg_list, acc =
       Util.mapfold (Mapfold.expression_it funs) acc arg_list in
     let e, acc =
       try
         apply funs acc f arg_list
       with
         Cannot_inline -> { e with e_desc = Eapp({ app with f; arg_list }) }, acc in
     e, acc
  | Eop(Erun i, [f; arg]) ->
     let f, acc = Mapfold.expression_it funs acc f in
     let arg, acc = Mapfold.expression_it funs acc arg in
     let e, acc =
       try
         apply funs acc f [arg]
       with
         Cannot_inline -> { e with e_desc = Eop(Erun i, [f; arg]) }, acc in
     e, acc
  | _ -> raise Mapfold.Fallback

let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQeq({ pat_desc = Evarpat(x) } as p, e) ->
     let x, acc = Mapfold.var_ident_it funs.global_funs acc x in
     let e, acc = Mapfold.expression_it funs acc e in
     let eq, acc =
       try
         let acc = make_subst acc x e in eq_empty, acc
       with Cannot_inline -> 
         { eq with eq_desc = EQeq({ p with pat_desc = Evarpat(x) }, e) }, acc in
     eq, acc
  | _ -> raise Mapfold.Fallback

(* all local names can restart from 0 *)
(* to be done later; for the moment, starts from the current value *)
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

(* a post-pass verification checking that all *)
(* [inline fun x1...xn -> e] have been removed *)
let check_no_inline_letdecl subst l_decl =
  let expression funs subst ({ e_desc; e_loc } as e) =
    match e_desc with
    | Evar(x) ->
       let e, subst =
         try
           let _ = Env.find x subst in
           Format.eprintf
             "@[%aInline error: this expression should be replaced by \
              an inlined function.@ \
              The inlining cannot be done because \
              it is not on the left of an application@ \
              or the application is partial.@.@]"
             Location.output_location e_loc;
           raise Misc.Error
         with | Not_found -> e, subst in
       e, subst
    | _ -> raise Mapfold.Fallback in

  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with global_funs; expression } in
  
  Mapfold.letdecl_it funs subst l_decl

let letdecl funs acc l_decl =
  let l_decl, ({ subst } as acc) = Mapfold.letdecl funs acc l_decl in
  let _ = check_no_inline_letdecl subst l_decl in
  l_decl, acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with
      global_funs; expression; equation; letdecl; set_index; get_index; } in
  let p, { renaming; subst } = Mapfold.program_it funs empty p in
  p


