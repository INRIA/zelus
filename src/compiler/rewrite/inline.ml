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

(* Inlining of function calls. Expressions [inline fun x1... -> e] *)
(* are eliminated. If an [inline fun x1... -> e] remains, inlining fails *)

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
  { f_inline: bool; (* the function must be inlined *)
    f_partial: bool; (* the function is the result of a partial application *)
    (* in that case, parameters do not need to be renamed anymore *)
    (* and [f_env] is correct. Still, names in [f_body] must be renamed *)
    f_kind: kind; (* the kind of the function *)
    f_args: Typinfo.arg list; (* the list of arguments *)
    f_body: Typinfo.result; (* the body *)
    f_env: Typinfo.ienv Env.t; (* the environment for parameters *)
    f_acc: acc (* the environment: renaming and substitution *)
  }
    
and acc =
  { renaming: Ident.t Env.t; (* renaming *)
    subst: value Env.t; (* substitution *)
  }

let empty = { renaming = Env.empty; subst = Env.empty }

let eq_empty = Aux.eqmake Defnames.empty EQempty
    
let append { subst = s } ({ subst } as acc) = 
  { acc with subst = Env.append s subst }

(* keep entries in [f_env] for names in [dv] *)
let keep f_env dv = Env.filter (fun x _ -> S.mem x dv) f_env

let fresh () = Ident.fresh "inline"

(* when [e] has value [v], add an entry [x\v] to [subst] *)
let value { subst } { e_desc } =
  match e_desc with
  | Eglobal { lname } ->
     let v =
       let open Global in
       try
         let { info = { value_exp } } = Modules.find_value lname in
         match value_exp with
         | Some(Vfun { f_inline; f_kind; f_args; f_body; f_env }) ->
            { f_inline; f_partial = false;
              f_kind; f_args; f_body; f_env; f_acc = empty }
         | _ -> raise Cannot_inline 
       with
       | Not_found -> raise Cannot_inline in
     v
  | Evar(y) ->
     let v = try Env.find y subst with Not_found -> raise Cannot_inline in v
  | _ -> raise Cannot_inline

let make_subst ({ subst } as acc) x e =
  { acc with subst = Env.add x (value acc e) subst }

(* given [f_param_1;...;f_param_n] and [arg1;...;arg_n] *)
(* define [f_param_1 = arg1;...; f_param_n = arg_n] *)
(* if [arg_i] is a value, the binding [f_param_i\arg_i] is added to [subst] *)
(* [acc] is the current environment in which [e] is evaluated. [acc] *)
(* is the environment augmented with new bindings *)
let match_f_param_with_arg_list acc f_acc (f_param_list, arg_list) =
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
  List.fold_left2 match_t ([], f_acc) f_param_list arg_list

(* Main Transformation *)
(* [(\a1...an. e) e1 ... en] 
 *- rewrites to:
 *- [local a1',...,an' do a1' = e1 ... an' = en in r[ai\ai']]
 *- [(\(a1 ... an returns p eq) e1 ... en
 *- rewrites to:
 *- [local a1',...,an', v_ret'
 *-  do a1' = e1 ... an' = en and eq[ai\ai'] in v_ret' *)
 let rec let_in funs acc loc 
           { f_inline; f_kind; f_partial; f_args = f_param_list;
             f_body; f_env; f_acc } arg_list =
   (* recursively treat the argument *)
   let params f_acc v_list =
     Util.mapfold (Mapfold.vardec_it funs) f_acc v_list in

   let match_f_param_with_arg_list acc f_acc (f_param_list, arg_list) =
     (* build a list of equations *)
     let eq_list, f_acc = 
       match_f_param_with_arg_list acc f_acc (f_param_list, arg_list) in
     
     eq_list, f_acc in

   let result_t f_acc eq_list result =
     (* inlining is done recursively on the body [result] *)
     let { r_desc } as result, f_acc = Mapfold.result_it funs f_acc result in
     let e = match r_desc with
       | Exp(r_e) ->
          Aux.e_let_list false eq_list r_e
       | Returns { b_vars; b_body } ->
          Aux.e_let_list false eq_list
            (Aux.e_let_list false [b_body]
               (Aux.returns_of_vardec_list_make b_vars)) in
     e, append f_acc acc in

   (* compute the arity *)
   let n_f_param_list = List.length f_param_list in
   let n_arg_list = List.length arg_list in
   
   (* build a renaming for the formal parameters *)
   let f_param_list, f_env, f_acc =
     if f_partial then
       (* parameters have already been renamed *)
       f_param_list, f_env, f_acc
     else
       (* rename the list of parameters *)
       let f_env, f_acc = Mapfold.build_it funs.global_funs f_acc f_env in
       let f_param_list, f_acc = Util.mapfold params f_acc f_param_list in  
       f_param_list, f_env, f_acc in
   if n_f_param_list = n_arg_list
   then
     let eq_list, f_acc =
       match_f_param_with_arg_list acc f_acc (f_param_list, arg_list) in
     result_t f_acc eq_list f_body
   else
     if n_f_param_list < n_arg_list then
       (* [(inline fun x1..xn -> result) e1..en en+1...em] *)
        let arg_list, arg_rest_list =
         Util.firsts_n n_f_param_list arg_list in
       let eq_list, f_acc =
         match_f_param_with_arg_list acc f_acc (f_param_list, arg_list) in
       let e, f_acc = result_t f_acc [] f_body in
       let e, f_acc = apply funs f_acc e arg_rest_list in
       Aux.e_let_list false eq_list e, f_acc
     else
       (* [n_f_param_list > n_arg_list] *)
       (* [(inline fun x1..xn xn+1..xm -> result) e1..en] *)
       let f_param_list, f_param_rest_list =
         Util.firsts_n n_arg_list f_param_list in
       let eq_list, f_acc =
         match_f_param_with_arg_list acc f_acc (f_param_list, arg_list) in
       (* keeps entries in [f_env] for names in [f_param_rest_list] *)
       let dv =
         List.fold_left
           (List.fold_left (fun acc { var_name } -> S.add var_name acc))
           S.empty f_param_rest_list in
       let f_env = keep f_env dv in
       let m = fresh () in
       let entry =
         { f_inline; f_partial = true;
           f_kind; f_args = f_param_rest_list; f_body = f_body;
           f_env; f_acc } in
       Aux.e_let_list false eq_list { (Aux.var m) with e_loc = loc },
       append { f_acc with subst = Env.add m entry f_acc.subst } acc

(* application *)
and apply funs ({ subst } as acc) ({ e_desc; e_loc } as e) arg_list =
  match e_desc with
  | Elet(l_eq, e_let) ->
     (* when the function apply is called, [e] has already been traversed *)
     (* so it is useless to pass again on [l_eq] *)
     let e_let, acc = apply funs acc e_let arg_list in
     { e with e_desc = Elet(l_eq, e_let) }, acc
  | _ ->
     let v = value acc e in
     let_in funs acc e_loc v arg_list

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
let expression funs ({ renaming; subst } as acc) ({ e_desc; e_loc } as e) = 
  match e_desc with
  | Efun({ f_inline = true; f_kind; f_args; f_body; f_env }) ->
     let m = fresh () in
     { e with e_desc = Evar(m) },
     { acc with subst =
                  Env.add m { f_inline = true; f_partial = false;
                              f_kind; f_args; f_body; f_env; f_acc = acc } 
                    subst }
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
  | Elet(leq, e_let) ->
     let leq, acc = Mapfold.leq_it funs acc leq in
     let e_let, acc = Mapfold.expression_it funs acc e_let in
     Aux.e_let_loc e_loc leq e_let, acc
  (* TODO: remove the operator Erun; mark function calls instead *)
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

let equation funs acc eq =
  let { eq_desc; eq_loc } as eq, acc = Mapfold.equation funs acc eq in
    match eq_desc with
    | EQeq({ pat_desc = Evarpat(x) } as p, e) ->
       let eq, acc =
         try
           let acc = make_subst acc x e in eq_empty, acc
         with Cannot_inline -> 
           { eq with eq_desc = EQeq({ p with pat_desc = Evarpat(x) }, e) }, 
           acc in
       eq, acc
    | EQlet(leq, eq_let) ->
       Aux.eq_let_loc eq_loc leq eq_let, acc
  | _ -> 
       eq, acc

let leq_t funs acc leq =
  let ({ l_eq; l_env } as leq), acc = Mapfold.leq_t funs acc leq in
  (* update [l_env] *)
  { leq with l_env = keep l_env (Defnames.names S.empty l_eq.eq_write) }, acc

(* all local names can restart from 0. For the moment, we start from the *)
(* current maximal value *)
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

(* a post-pass verification checking that all *)
(* [inline fun x1...xn -> e] have been removed *)
let check_no_inline_letdecl subst l_decl =
  let error loc f_kind f_args =
    let module Printer = Printer.Make(Ptypinfo) in
    let fun_arg_list ff (kind, f_args) =
      Format.eprintf
        "@[inline %s %a -> ...@]" (Printer.kind f_kind)
        Printer.arg_list f_args in
    Format.eprintf
      "@[%aInline error: this expression should be replaced by \
       an inlined function@ \
       [%a]@ The inlining cannot be done because \
       it is not on the left of an application@ \
       or the application is partial.@.@]"
      Location.output_location loc
      fun_arg_list (f_kind, f_args);
    raise Misc.Error in
  
  let expression funs subst ({ e_desc; e_loc } as e) =
    match e_desc with
    | Eglobal { lname } ->
       let r =
         let open Global in
         try
           let { info = { value_exp } } = Modules.find_value lname in
           match value_exp with
           | Some(Vfun { f_inline; f_kind; f_args }) ->
              if f_inline then error e_loc f_kind f_args else e, subst
           | _ -> e, subst
         with
         | Not_found -> e, subst in
       r
    | Evar(x) ->
       let r = 
         try
           let { f_inline; f_kind; f_args } = Env.find x subst in
           if f_inline then error e_loc f_kind f_args else e, subst
         with | Not_found -> e, subst in
       r
    | _ -> raise Mapfold.Fallback in

  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with global_funs; expression } in
  
  Mapfold.letdecl_it funs subst l_decl

let letdecl funs acc (d_names, d_leq) =
  let d_leq, ({ subst; renaming } as acc) = Mapfold.leq_it funs empty d_leq in
  (* every entry in [subst] is added to the global symbol table *)
  let update_module_table d_names (name, m) =
    let m_copy, _ = Mapfold.var_ident_it funs.global_funs acc m in
    try
      let { f_inline; f_args; f_kind; f_body; f_env } =
        Env.find m_copy subst in
      let entry = Modules.find_value (Name name) in
      Global.set_value_exp entry
        (Global.Vfun { Global.f_inline; 
                       Global.f_args; Global.f_kind;
                       Global.f_body; Global.f_env });
      (* entry [name, m] is removed from the list of defined names *)
      d_names
    with
      Not_found -> (name, m_copy) :: d_names in
  let d_names = List.fold_left update_module_table [] d_names in
  
  let _ = check_no_inline_letdecl subst (d_names, d_leq) in
  (d_names, d_leq), acc

let open_t funs acc modname =
  Modules.open_module modname;
  modname, acc

(* useful function; remove empty declarations [let ()] *)
let not_empty { desc } = match desc with
  | Eletdecl { d_leq = { l_eq } } when Aux.is_empty l_eq -> false | _ -> true
  
let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with
      global_funs; expression; equation; leq_t; letdecl; open_t;
      set_index; get_index; } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  let p_impl_list = List.filter not_empty p_impl_list in
  { p with p_impl_list }
