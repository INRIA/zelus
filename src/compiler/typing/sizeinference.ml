(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2023 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* size inference. *)
(* must be done after typing *)

open Ident
open Global
open Modules
open Zelus
open Deftypes
open Types
open Typing

(* A size constraint is a conjunction of constraints *)
(* (size1 = 0) /\ (... = 0) /\ (sizen = 0) *)
type size_constraint =
  | Conj :
      size_constraint list -> size_constraint
  | Czero :
      { size: Deftypes.size; loc: Location.t } -> sconstraint
  | Cempty : size_constraint

(* satisfiable *)
(* (x - y = 0) /\ ... /\ (z + y + 2 * m) = 0 *)


(* [expression h e] returns the type for [e] and [sconstraint] *)
let expression h ({ e_desc; e_loc; e_typ } as e) =
  let ty, c = match e_desc with
    | Econst(i) -> e_typ, Cempty
    | Elocal(x) ->
       let { t_typ = typ } = var h x in
       typ, Cempty
    | Eglobal ({ lname = lname } as g) ->
       let ty = gvar lname in
       ty, Cempty
    | Elast(x) -> last h x, Cempty
    | Etuple(e_list) ->
       let ty_c_list = List.map (expression h) e_list in
       let ty_list, c_list = List.split ty_c_list in
       product ty_list, Conj(c_list)
    | Eop(op, e_list) ->
       operator e_loc h op e_list
    | Eapp(f, arg_list) ->
       apply e_loc h f arg_list
    | Econstr0({ lname } as c) ->
       let qualid, { constr_res = ty_res; constr_arity = n } =
         get_constr e_loc lname in
       if n <> 0 then error e_loc (Econstr_arity(lname, n, 0));
       c.lname <- Lident.Modname(qualid);
       ty_res, Tfun(Tconst)
    | Econstr1({ lname; arg_list } as c) ->
       let qualid,
           { constr_arg = ty_list; constr_res = ty_res; constr_arity = n } =
         get_constr e_loc lname in
       let actual_arity = List.length arg_list in
       if n <> actual_arity then
         error e_loc (Econstr_arity(lname, n, actual_arity));
       let actual_k_list = List.map2 (expect expected_k h) arg_list ty_list in
       c.lname <- Lident.Modname(qualid);
       ty_res, Kind.sup_list actual_k_list
    | Erecord_access({ label; arg } as r) ->
       let qualid, { label_arg = ty_arg; label_res = ty_res } =
         get_label e_loc label in
       let actual_k = expect expected_k h arg ty_arg in
       r.label <- Lident.Modname(qualid);
       ty_res, actual_k
    | Erecord(label_e_list) ->
       let ty = new_var () in
       let actual_k_list =
         List.map (type_label_arg expected_k ty h e_loc) label_e_list in
       (* check that no field is missing *)
       let label_desc_list = get_all_labels e_loc ty in
       if List.length label_e_list <> List.length label_desc_list
       then error e_loc Esome_labels_are_missing;
       ty, Kind.sup_list actual_k_list
    | Erecord_with(e1, label_e_list) ->
       let ty = new_var () in
       let actual_k_list =
         List.map (type_label_arg expected_k ty h e_loc) label_e_list in
       let actual_k = expect expected_k h e1 ty in
       ty, Kind.sup actual_k (Kind.sup_list actual_k_list)
    | Etypeconstraint(exp, typ_expr) ->
       let expected_typ =
         Types.instance_of_type (Interface.scheme_of_type typ_expr) in
       let actual_k = expect expected_k h exp expected_typ in
       expected_typ, actual_k
    | Elet(l, e) ->
       let h, actual_k = leq expected_k h l in
       let ty, actual_k_e = expression expected_k h e in
       ty, Kind.sup actual_k actual_k_e
    | Efun(fe) ->
       (* functions are only allowed in a static context *)
       less_than e_loc expected_k (Tfun(Tstatic));
       let ty = funexp h fe in
       ty, expected_k
    | Ematch({ is_total; e; handlers } as mh) ->
        let expected_pat_ty, actual_pat_k = expression expected_k h e in
        let expected_ty = new_var () in
        let is_total, actual_k_h =
          match_handler_exp_list
            e_loc expected_k h is_total handlers expected_pat_ty expected_ty in
        mh.is_total <- is_total;
        expected_ty, Kind.sup actual_pat_k actual_k_h
    | Epresent { handlers; default_opt } ->
        let expected_ty = new_var () in
        let actual_k =
          present_handler_exp_list
            e_loc expected_k h handlers default_opt expected_ty in
        expected_ty, actual_k
    | Ereset(e_body, e_res) ->
       let ty, actual_k_body = expression expected_k h e_body in
       let actual_k = expect expected_k h e_res Initial.typ_bool in
       ty, Kind.sup actual_k_body actual_k
    | Eassert(e_body) ->
       let actual_k = expect expected_k h e Initial.typ_bool in
       Initial.typ_unit, actual_k in
  (* type annotation *)
  e.e_typ <- ty;
  ty, actual_k

and type_label_arg expected_k expected_ty h loc ({ label; arg } as r) =
  let qualid, { label_arg = ty_arg; label_res = ty_res } =
    get_label loc label in
  unify_expr arg expected_ty ty_arg;
  let actual_k = expect expected_k h arg ty_res in
  r.label <- Lident.Modname(qualid);
  actual_k

(** The type of primitives and imported functions **)
and operator expected_k h loc op e_list =
  let actual_k, ty_args, ty_res =
    match op with
    | Eifthenelse ->
        let ty = new_var () in
        Tfun(Tconst), [Initial.typ_bool; ty; ty], ty
    | Eunarypre ->
        let ty = new_var () in
        Tnode(Tdiscrete), [ty], ty
    | (Eminusgreater | Efby) ->
        let ty = new_var () in
        Tnode(Tdiscrete), [ty; ty], ty
    | Erun _ ->
       let ty1 = new_var () in
       let ty2 = new_var () in
       Tnode(Tdiscrete), [ty1], ty2
    | Eseq ->
       let ty = new_var () in
       Tfun(Tconst), [Initial.typ_unit; ty], ty
    | Eatomic ->
       let ty = new_var () in
       Tfun(Tconst), [ty], ty
    | Etest ->
       let ty = new_var () in
       Tfun(Tconst), [Initial.typ_signal ty], Initial.typ_bool
    | Eup ->
       Tnode(Thybrid), [Initial.typ_float], Initial.typ_zero
    | Eperiod ->
       Tfun(Tconst), [Initial.typ_float; Initial.typ_float], Initial.typ_zero
    | Ehorizon ->
       Tnode(Thybrid), [Initial.typ_float], Initial.typ_zero
    | Edisc ->
       Tnode(Thybrid), [Initial.typ_float], Initial.typ_zero
    | Earray(op) ->
       let actual_k, ty_args, ty_res =
         match op with
         | Earray_list ->
            let ty = new_var () in
            Tfun(Tconst), List.map (fun _ -> ty) e_list, Initial.typ_array ty
         | Econcat ->
            let ty = Initial.typ_array (new_var ()) in
            Tfun(Tconst), [ty; ty], ty
         | Eget ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty; Initial.typ_int], ty
         | Eget_with_default ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty; Initial.typ_int; ty], ty
         | Eslice ->
            let ty = Initial.typ_array (new_var ()) in
            Tfun(Tconst), [ty; ty], ty
         | Eupdate ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty; Initial.typ_int; ty],
            Initial.typ_array ty
         | Etranspose ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array (Initial.typ_array ty)],
            Initial.typ_array (Initial.typ_array ty)
         | Ereverse ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty], Initial.typ_array ty
         | Eflatten ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array (Initial.typ_array ty)],
            Initial.typ_array ty in
       actual_k, ty_args, ty_res in
  less_than loc actual_k expected_k;
  let actual_k_list =
    List.map2 (expect expected_k h) e_list ty_args in
  ty_res, Kind.sup actual_k (Kind.sup_list actual_k_list)

and funexp h ({ f_kind; f_args; f_body } as body) =
  let expected_k = Interface.kindtype f_kind in
  let h_args, _, ty_arg_list = arg_list expected_k h f_args in
  body.f_env <- h_args;
  (* type the body *)
  let h = Env.append h_args h in
  let ty_res, _ = result expected_k h f_body in
  (* returns a type *)
  Types.arrowtype_list expected_k ty_arg_list ty_res

and arg_list expected_k h args =
  let h_args, actual_k_args =
    List.fold_left
      (fun (acc_h, acc_k) arg ->
        vardec_list expected_k (Env.append acc_h h) arg)
      (Env.empty, Tfun(Tconst)) args in
  let ty_args =
    List.map (type_of_vardec_list h_args) args in
  h_args, actual_k_args, ty_args
  
(* Typing the result of a function *)
and result expected_k h ({ r_desc } as r) =
  let ty, actual_k =
    match r_desc with
    | Exp(e) ->
       let ty, actual_k = expression expected_k h e in
       ty, actual_k
    | Returns ({ b_vars } as b) ->
       let _, new_h, _, actual_k = block_eq expected_k h b in
       type_of_vardec_list new_h b_vars, actual_k in
  (* type annotation *)
  r.r_typ <- ty;
  ty, actual_k

(* Typing an expression with expected type [expected_type] **)
and expect expected_k h e expected_ty =
  let actual_ty, actual_k = expression expected_k h e in
  unify_expr e expected_ty actual_ty;
  actual_k


(** Typing an application **)
and apply loc expected_k h e arg_list =
  (* first type the function body *)
  let ty_fct, actual_k_fct = expression expected_k h e in
  (* typing the list of arguments *)
  let rec args actual_k_fct ty_fct = function
    | [] -> ty_fct, actual_k_fct
    | arg :: arg_list ->
       let arg_k, ty1, ty2 =
         try Types.filter_arrow (Tfun(Tany)) ty_fct
         with Unify -> error loc (Eapplication_of_non_function) in
       let expected_arg_k =
         match arg_k with
         | Tfun(Tconst) | Tfun(Tstatic) -> arg_k
         | _ -> expected_k in
       let actual_k_arg = expect expected_arg_k h arg ty1 in
       let actual_k_fct =
         match actual_k_fct, arg_k with
         (* |-const f : t -A-> t' and |-k e: t then |-k f e: t' *)
         | Tfun(Tconst), Tfun _ -> actual_k_arg
         (* |-static f : t -A-> t' and |-k e: t then |-static\/k f e: t' *)
         | Tfun(Tstatic), Tfun _ -> Kind.sup actual_k_fct actual_k_arg
         | _ -> Kind.sup actual_k_fct (Kind.sup arg_k actual_k_arg) in
       args actual_k_fct ty2 arg_list in
  args actual_k_fct ty_fct arg_list

(** Typing an equation. Returns the set of defined names **)
and equation expected_k h { eq_desc; eq_loc } =
  match eq_desc with
  | EQeq(p, e) ->
     let ty_e, actual_k = expression expected_k h e in
     pattern h p ty_e;
     (* check that the pattern is total *)
     check_total_pattern p;
     let dv = Write.fv_pat S.empty p in
     { Deftypes.empty with dv = dv }, actual_k
  | EQder(n, e, e0_opt, handlers) ->
     (* a derivative is only possible in a stateful context *)
     less_than eq_loc (Tnode(Thybrid)) expected_k;
     let actual_ty = der eq_loc h n in
     let _ = expect expected_k h e actual_ty in
     unify eq_loc Initial. typ_float actual_ty;
     let di =
       match e0_opt with
       | None -> S.empty
       | Some(e) ->
          let _ = expect expected_k h e Initial.typ_float in
          let _ = init eq_loc h n in S.singleton n in
     ignore (present_handler_exp_list
               eq_loc expected_k h handlers NoDefault Initial.typ_float);
     { Deftypes.empty with di = di; der = S.singleton n }, Tnode(Thybrid)
  | EQinit(n, e0) ->
     (* an initialization is valid only in a stateful context *)
     stateful eq_loc expected_k;
     let actual_ty = init eq_loc h n in
     let _ = expect expected_k h e0 actual_ty in
     { Deftypes.empty with di = S.singleton n }, expected_k
  | EQemit(n, e_opt) ->
     let ty_e = new_var () in
     let actual_ty = typ_of_var eq_loc h n in
     let actual_k =
       match e_opt with
       | None ->
          unify eq_loc (Initial.typ_signal Initial.typ_unit) actual_ty;
          Tfun(Tconst)
       | Some(e) ->
          unify eq_loc (Initial.typ_signal ty_e) actual_ty;
          expect expected_k h e ty_e in
     { Deftypes.empty with dv = S.singleton n }, actual_k
  | EQautomaton({ is_weak; handlers; state_opt }) ->
     (* automata are only valid in a statefull context *)
     stateful eq_loc expected_k;
     automaton_handlers_eq is_weak eq_loc expected_k h handlers state_opt
  | EQmatch({ is_total; e; handlers } as mh) ->
     let expected_pat_ty, actual_k_e = expression expected_k h e in
     let is_total, defnames, actual_k_h =
       match_handler_eq_list
         eq_loc expected_k h is_total handlers expected_pat_ty in
     mh.is_total <- is_total;
     defnames, Kind.sup actual_k_e actual_k_h
  | EQif(e, eq1, eq2) ->
     let actual_k_e = expect expected_k h e Initial.typ_bool in
     let defnames1, actual_k_eq1 = equation expected_k h eq1 in
     let defnames2, actual_k_eq2 = equation expected_k h eq2 in
     Total.merge eq_loc h [defnames1; defnames2],
     Kind.sup actual_k_e (Kind.sup actual_k_eq1 actual_k_eq2)
  | EQpresent({ handlers; default_opt }) ->
     present_handler_eq_list eq_loc expected_k h handlers default_opt
  | EQreset(eq, e) ->
     let actual_k_e = expect expected_k h e Initial.typ_bool in
     let defnames, actual_k_eq =
       equation expected_k h eq in
     defnames, Kind.sup actual_k_e actual_k_eq
  | EQand(eq_list) -> equation_list expected_k h eq_list
  | EQempty -> Deftypes.empty, Tfun(Tconst)
  | EQlocal(b_eq) ->
     let _, _, defnames, actual_k = block_eq expected_k h b_eq in
     defnames, actual_k
  | EQlet(l_eq, eq) ->
     let h, actual_k = leq expected_k h l_eq in
     let defnames, actual_k_eq = equation expected_k h eq in
     defnames, Kind.sup actual_k actual_k_eq
  | EQassert(e) ->
     let actual_k = expect expected_k h e Initial.typ_bool in
     Deftypes.empty, actual_k

and equation_list expected_k h eq_list =
  List.fold_left
    (fun (defined_names, actual_k) eq ->
      let defined_names_eq, actual_k_eq = equation expected_k h eq in
      Total.join eq.eq_loc defined_names_eq defined_names,
    Kind.sup actual_k_eq actual_k)
    (Deftypes.empty, Tfun(Tconst)) eq_list

(** Type a present handler when the body is an expression or equation **)
and present_handler_exp_list loc expected_k h p_h_list default_opt expected_ty =
  let _, actual_k =
    present_handlers scondpat
      (fun expected_k h e expected_ty ->
        let actual_k = expect expected_k h e expected_ty in
        Deftypes.empty, actual_k)
      loc expected_k h p_h_list default_opt expected_ty in
  actual_k

and present_handler_eq_list loc expected_k h eq_h_list eq_opt =
  present_handlers scondpat
    (fun expected_k h eq _ -> equation expected_k h eq)
    loc expected_k h eq_h_list eq_opt Initial.typ_unit

(** Type a match handler when the body is an expression or equation **)
and match_handler_eq_list loc expected_k h is_total eq_h_list pat_ty =
  match_handlers
    (fun expected_k h eq _ -> equation expected_k h eq)
    loc expected_k h is_total eq_h_list pat_ty Initial.typ_unit

and match_handler_exp_list loc expected_k h total m_h_list pat_ty ty =
  let is_total, _, actual_k =
    match_handlers
      (fun expected_k h e expected_ty ->
        let actual_k = expect expected_k h e expected_ty in
        Deftypes.empty, actual_k)
      loc expected_k h total m_h_list pat_ty ty in
  is_total, actual_k

(** Type an automaton handler when the body is an equation **)
and automaton_handlers_eq is_weak loc expected_k h handlers se_opt =
  let block_eq expected_k h ({ b_vars; b_body } as b) =
    let _, h, defined_names, actual_k = block_eq expected_k h b in
    h, defined_names, actual_k in
  let defined_names, _ =
    automaton_handlers scondpat leqs block_eq block_eq state_expression
      is_weak loc expected_k h handlers se_opt in
  (* the actual kind is necessarily stateful *)
  defined_names, expected_k

and block_eq expected_k h ({ b_vars; b_body } as b) =
  let h0, actual_k_h0 = vardec_list expected_k h b_vars in
  let h = Env.append h0 h in
  let defined_names, actual_k_body = equation expected_k h b_body in
  (* check that every name in [n_list] has a definition *)
  let defined_names =
    check_definitions_for_every_name defined_names b_vars in
  b.b_env <- h0;
  b.b_write <- defined_names;
  h0, h, defined_names, Kind.sup actual_k_h0 actual_k_body

and leq expected_k h ({ l_rec; l_eq } as l) =
  let h0 = env_of_equation l_eq in
  l.l_env <- h0;
  let new_h = Env.append h0 h in
  let _, actual_k = equation expected_k new_h l_eq in
  new_h, actual_k

and leqs expected_k h l =
  List.fold_left
    (fun (h, acc_k) l_eq ->
      let h, actual_k = leq expected_k h l_eq in
      h, Kind.sup acc_k actual_k) (h, Tfun(Tconst)) l
  
(** Typing a signal condition **)
and scondpat expected_k type_of_condition h scpat =
  let rec typrec expected_k scpat =
    match scpat.desc with
    | Econdand(sc1, sc2) ->
       let actual_k1 = typrec expected_k sc1 in
       let actual_k2 = typrec expected_k sc2 in
       Kind.sup actual_k1 actual_k2
    | Econdor(sc1, sc2) ->
       let actual_k1 = typrec expected_k sc1 in
       let actual_k2 = typrec expected_k sc2 in
       Kind.sup actual_k1 actual_k2
    | Econdexp(e) ->
       expect expected_k h e type_of_condition
    | Econdpat(e_cond, pat) ->
       (* check that e is a signal *)
       let ty = new_var () in
       let actual_k = expect expected_k h e_cond (Initial.typ_signal ty) in
       pattern h pat ty;
       actual_k
    | Econdon(sc1, e) ->
       let actual_k1 = typrec expected_k sc1 in
       (* we impose that [e] is a combinatorial expression *)
       (* not to have state variable that evolve only when [sc1] is true *)
       let actual_k = expect (Tfun(Tany)) h e Initial.typ_bool in
       Kind.sup actual_k1 actual_k in
  typrec expected_k scpat


(* typing state expressions. [state] must be a stateless expression *)
(* [actual_reset = true] if [state] is entered by reset *)
and state_expression h def_states actual_reset { desc; loc } = 
  match desc with
  | Estate0(s) ->
     begin try
         let ({ s_reset = expected_reset; s_parameters = args } as r) =
           Env.find s def_states in
         if args <> []
         then error loc (Estate_arity_clash(s, 0, List.length args));
         r.s_reset <-
           check_target_state loc expected_reset actual_reset;
         Tfun(Tconst)
       with
       | Not_found -> error loc (Estate_unbound s)
     end
  | Estate1(s, l) ->
     let ({ s_reset = expected_reset; s_parameters = args } as r) =
       try
         Env.find s def_states
       with
       | Not_found -> error loc (Estate_unbound s) in
     begin try
         (* we impose that [e] is combinatorial *)
         let actual_k_list =
           List.map2
             (fun e expected_ty -> expect (Tfun(Tany)) h e expected_ty)
             l args in
         r.s_reset <-
           check_target_state loc expected_reset actual_reset;
         Kind.sup_list actual_k_list
       with
       | Invalid_argument _ ->
          error loc
            (Estate_arity_clash(s, List.length l, List.length args))
     end
  | Estateif(e, se1, se2) ->
     (* we impose that [e] is combinatorial *)
     let actual_k = expect (Tfun(Tany)) h e Initial.typ_bool in
     let actual_k1 = state_expression h def_states actual_reset se1 in
     let actual_k2 = state_expression h def_states actual_reset se2 in
     Kind.sup actual_k (Kind.sup actual_k1 actual_k2)

     
let implementation ff is_first { desc; loc } =
  try
    match desc with
    | Eopen(modname) ->
       if is_first then Modules.open_module modname
    | Eletdecl { name; const; e } ->
       Misc.push_binding_level ();
       (* a value a top level must be static. As it is the bottom kind *)
       (* no need to return it *)
       let expected_k = Tfun(if const then Tconst else Tstatic) in
       let ty, _ = expression expected_k Env.empty e in
       (* check that the type is well formed *)
       type_is_in_kind loc Tstatic ty;
       Misc.pop_binding_level ();
       let tys = Types.gen (not (expansive e)) ty in
       if is_first then Interface.add_type_of_value ff loc name const tys
       else Interface.update_type_of_value ff loc name const tys
    | Etypedecl { name; ty_params; size_params; ty_decl } ->
       if is_first then
         Interface.typedecl ff loc name size_params ty_params ty_decl
  with
  | Typerrors.Error(loc, err) ->
     if is_first then Typerrors.message loc err
     else
       begin
         Format.eprintf
           "@[Internal error: type error during the second step \n\
            after static reduction and inlining\n\
            Be carreful, the localisation of errors is misleading@.@.@]";
         Typerrors.message loc err
       end

(* the main entry function *)
let program ff is_first impl_list =
  Misc.no_warning := not is_first;
  List.iter (implementation ff is_first) impl_list;
  Misc.no_warning := not is_first;
  impl_list

let implementation_list = program
