(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(** compile-time elimination of static expressions and polymorphic values *)
(** this performs strong normalisation, i.e., reduction under lambdas *)
(** for functions that only have dynamically known inputs. *)
(** The result is a collection of first-order functions *)

open Misc
open Ident
open Lident
open Global
open Zelus
open Zaux
open Static
open Deftypes
open Types

       
(* the list of functions introduced during the reduction *)
type fun_defs = { fundefs : (name * funexp) list }

let empty = { fundefs =[] }
	      
(* Generate fresh symbol names for global values introduced during *)
(* the reduction *)
let num = ref 0
let fresh () = num := !num + 1; "__" ^ (string_of_int !num)
					 
(** Simplify an expression. [expression env fun_defs e = e', fun_defs'] *)
(* - env an environment of values;
   - e and e' are expressions;
   - fun_defs and fun_defs' are list of the functions introduced 
     during the simplification *)
let rec expression env fun_defs ({ e_desc = desc } as e) =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e, fun_defs
  | Elocal(x) | Elast(x) ->
     let e, fun_defs =
       try exp_of_value fun_defs (Env.find x env)
       with Not_found -> e, fun_defs in
     e, fun_defs
  | Eperiod _ -> e, fun_defs
  | Etuple(e_list) ->
     let e_list, fun_defs = Misc.map_fold (expression env) fun_defs e_list in
     { e with e_desc = Etuple(e_list) }, fun_defs
  | Erecord(l_e_list) -> 
     let l_e_list, fun_defs =
       Misc.map_fold
	 (fun fun_defs (ln, e) ->
	  let e, fun_defs = expression env fun_defs e in
	  (ln, e), fun_defs) fun_defs l_e_list in
       { e with e_desc = Erecord(l_e_list) }, fun_defs
  | Erecord_access(e_record, ln) ->
     let e_record, fun_defs = expression env fun_defs e_record in
     { e_record with e_desc = Erecord_access(e, ln) }, fun_defs
  | Eapp(app, e_fun, e_list) ->
     (* [e_fun] is necessarily static *)
     (* [e_list] decomposes into (a possibly empty) sequence of 
      * static arguments [s_list] and non static ones [ne_list] *)
     let v_fun = Static.expression env e_fun in
     let s_list, ne_list, ty_res =
       Types.split_arguments e_fun.e_typ e_list in
     let { value_exp = v; value_name = opt_name } as v_fun =
       Static.app v_fun (List.map (Static.expression env) s_list) in
     let e, fun_defs =
       match ne_list with
       | [] ->
	  let e, fun_defs = exp_of_value fun_defs v_fun in
	  { e with e_typ = ty_res }, fun_defs
       | _ ->
	  let ne_list, fun_defs =
	    Misc.map_fold (expression env) fun_defs ne_list in
	  (* two solutions are possible. Either we introduce a fresh *)
	  (* function [f] for the result of [v_fun s1...sn] *)
	  (* and return [f ne1...nek]. [f] could then be shared in case *)
	  (* several instance of [v_fun s1...sn] exist *)
	  (* Or we directly inline the body of [f]. We take this solution *)
	  (* at the moment *)
	  match opt_name, v with
	  | None, Vfun({ f_args = p_list; f_body = e; f_env = nenv }, env) ->
	     let e, fun_defs = expression env fun_defs e in
	     (* return [let p1 = ne1 in ... in pk = nek in e] *)
	     (* all names in [e] must be renamed *)
	     Inline.letin Env.empty nenv p_list ne_list e, fun_defs
	  | _ -> (* returns an application *)
	     let e_fun, fundefs = exp_of_value fun_defs v_fun in
	     let e_fun = { e_fun with e_typ = ty_res } in
	     { e with e_desc = Eapp(app, e_fun, ne_list) }, fun_defs in
     e, fun_defs
  | Eop(op, e_list) ->
     let e_list, fun_defs = Misc.map_fold (expression env) fun_defs e_list in
     { e with e_desc = Eop(op, e_list) }, fun_defs
  | Etypeconstraint(e_ty, ty) ->
     let e_ty, fun_defs = expression env fun_defs e_ty in
     { e with e_desc = Etypeconstraint(e_ty, ty) }, fun_defs
  | Eseq(e1, e2) ->
     let e1, fun_defs = expression env fun_defs e1 in
     let e2, fun_defs = expression env fun_defs e2 in
     { e with e_desc = Eseq(e1, e2) }, fun_defs
  | Elet(l, e_let) ->
     let l, fun_defs = local env fun_defs l in
     let e_let, fun_defs = expression env fun_defs e_let in
     { e with e_desc = Elet(l, e_let) }, fun_defs
  | Eblock({ b_locals = l_list; b_body = eq_list } as b, e_block) ->
     let l_list, fun_defs = Misc.map_fold (local env) fun_defs l_list in
     let eq_list, fun_defs = Misc.map_fold (equation env) fun_defs eq_list in
     let e_block, fun_defs = expression env fun_defs e_block in
     { e with e_desc =
		Eblock({ b with b_locals = l_list; b_body = eq_list },
		       e_block)  },
     fun_defs
  | Epresent _ | Ematch _ -> assert false

(* evaluate an static expression and turn it into an expression *)
(* preserve the type of [e] *)
and static env fun_defs e =
  let v = Static.expression env e in
  let { e_desc = desc }, fun_defs = exp_of_value fun_defs v in
  { e with e_desc = desc }, fun_defs
       
(** Simplify a local declaration *)
and local env fun_defs ({ l_eq = eq_list } as l) =
  let eq_list, fun_defs = Misc.map_fold (equation env) fun_defs eq_list in
  { l with l_eq = eq_list }, fun_defs

(** Simplify an equation. *)
and equation env fun_defs ({ eq_desc = desc } as eq) = 
  match desc with
  | EQeq(p, e) ->
     let e, fun_defs = expression env fun_defs e in
     { eq with eq_desc = EQeq(p, e) }, fun_defs
  | EQmatch(total, e, m_b_list) ->
     let e, fun_defs = expression env fun_defs e in
     let m_b_list, fun_defs =
       Misc.map_fold
	 (fun fun_defs ({ m_body = b } as mh) ->
	  let b, fun_defs = block env fun_defs b in
	  { mh with m_body = b }, fun_defs)
	 fun_defs m_b_list in
     { eq with eq_desc = EQmatch(total, e, m_b_list) }, fun_defs
  | EQblock(b) ->
     let b, fun_defs = block env fun_defs b in
     { eq with eq_desc = EQblock(b) }, fun_defs
  | EQpluseq(x, e) ->
     let e, fun_defs = expression env fun_defs e in
     { eq with eq_desc = EQpluseq(x, e) }, fun_defs
  | EQinit(x, e) ->
     let e, fun_defs = expression env fun_defs e in
     { eq with eq_desc = EQinit(x, e) }, fun_defs
  | EQnext(x, e, e_opt) ->
     let e, fun_defs = expression env fun_defs e in
     let e_opt, fun_defs =
       Misc.optional_with_map (expression env) fun_defs e_opt in
     { eq with eq_desc = EQnext(x, e, e_opt) }, fun_defs
  | EQder(x, e, e_opt, p_e_list) ->
     let body fun_defs ({ p_cond = scpat; p_body = e } as p_e) =
       let scpat, fun_defs = scondpat env fun_defs scpat in
       let e, fun_defs = expression env fun_defs e in
       { p_e with p_cond = scpat; p_body = e }, fun_defs in
     let e, fun_defs = expression env fun_defs e in
     let e_opt, fun_defs =
       Misc.optional_with_map (expression env) fun_defs e_opt in
     let p_e_list, fun_defs = Misc.map_fold body fun_defs p_e_list in
     { eq with eq_desc = EQder(x, e, e_opt, p_e_list) }, fun_defs
  | EQreset(eq_list, e) ->
     let e, fun_defs = expression env fun_defs e in
     let eq_list, fun_defs = Misc.map_fold (equation env) fun_defs eq_list in
     { eq with eq_desc = EQreset(eq_list, e) }, fun_defs
  | EQpar(par_eq_list) ->
     let par_eq_list, fun_defs =
       Misc.map_fold (equation env) fun_defs par_eq_list in
     { eq with eq_desc = EQpar(par_eq_list) }, fun_defs
  | EQseq(seq_eq_list) ->
     let seq_eq_list, fun_defs =
       Misc.map_fold (equation env) fun_defs seq_eq_list in
     { eq with eq_desc = EQseq(seq_eq_list) }, fun_defs
  | EQpresent(p_h_list, b_opt) ->
     let body fun_defs ({ p_cond = scpat; p_body = b } as p_b) =
       let scpat, fun_defs = scondpat env fun_defs scpat in
       let b, fun_defs = block env fun_defs b in
       { p_b with p_cond = scpat; p_body = b }, fun_defs in
     let b_opt, fun_defs = Misc.optional_with_map (block env) fun_defs b_opt in
     let p_h_list, fun_defs = Misc.map_fold body fun_defs p_h_list in
     { eq with eq_desc = EQpresent(p_h_list, b_opt) }, fun_defs
  | EQemit(x, e_opt) ->
     let e_opt, fun_defs =
       Misc.optional_with_map (expression env) fun_defs e_opt in
     { eq with eq_desc = EQemit(x, e_opt) }, fun_defs
  | EQautomaton(is_weak, s_h_list, se_opt) ->
     let state_exp env fun_defs ({ desc = desc } as se) =
       match desc with
       | Estate0 _ -> se, fun_defs
       | Estate1(x, e_list) ->
	  let e_list, fun_defs =
	    Misc.map_fold (expression env) fun_defs e_list in
	  { se with desc = Estate1(x, e_list) }, fun_defs in
     let escape env fun_defs ({ e_cond = scpat; e_block = b_opt;
			      e_next_state = se } as esc) =
       let scpat, fun_defs = scondpat env fun_defs scpat in
       let b_opt, fun_defs =
	 Misc.optional_with_map (block env) fun_defs b_opt in
       let se, fun_defs = state_exp env fun_defs se in
       { esc with e_cond = scpat; e_block = b_opt; e_next_state = se },
       fun_defs in
     let body env fun_defs ({ s_body = b; s_trans = esc_list } as h) =
       let b, fun_defs = block env fun_defs b in
       let esc_list, fun_defs =
	 Misc.map_fold (escape env) fun_defs esc_list in
       { h with s_body = b; s_trans = esc_list }, fun_defs in
     let s_h_list, fun_defs =
       Misc.map_fold (body env) fun_defs s_h_list in
     let se_opt, fun_defs =
       Misc.optional_with_map (state_exp env) fun_defs se_opt in
     { eq with eq_desc =
		 EQautomaton(is_weak, s_h_list, se_opt) }, fun_defs
  | EQforall({ for_index = i_list; for_init = init_list;
	       for_body = b_eq_list } as forall_body) ->
     let index env fun_defs ({ desc = desc } as ind) =
       match desc with
       | Einput(x, e) ->
	  let e, fun_defs = expression env fun_defs e in
	  { ind with desc = Einput(x, e) }, fun_defs
       | Eoutput _ -> ind, fun_defs
       | Eindex(x, e1, e2) ->
	  let e1, fun_defs = static env fun_defs e1 in
	  let e2, fun_defs = static env fun_defs e2 in
	  { ind with desc = Eindex(x, e1, e2)}, fun_defs in
     let init env fun_defs ({ desc = desc } as ini) =
	 match desc with
	 | Einit_last(x, e) ->
	    let e, fun_defs = expression env fun_defs e in
	    { ini with desc = Einit_last(x, e) }, fun_defs
	 | Einit_value(x, e, c_opt) ->
	    let e, fun_defs = expression env fun_defs e in
	    { ini with desc = Einit_value(x, e, c_opt) }, fun_defs in
     let i_list, fun_defs = Misc.map_fold (index env) fun_defs i_list in
     let init_list, fun_defs = Misc.map_fold (init env) fun_defs init_list in
     let b_eq_list, fun_defs = block env fun_defs b_eq_list in
     { eq with eq_desc =
		 EQforall { forall_body with for_index = i_list;
					     for_init = init_list;
					     for_body = b_eq_list } }, fun_defs
           
and scondpat env fun_defs ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     let scpat1, fun_defs = scondpat env fun_defs scpat1 in
     let scpat2, fun_defs = scondpat env fun_defs scpat2 in
     { scpat with desc = Econdand(scpat1, scpat2) }, fun_defs
  | Econdor(scpat1, scpat2) ->
     let scpat1, fun_defs = scondpat env fun_defs scpat1 in
     let scpat2, fun_defs = scondpat env fun_defs scpat2 in
     { scpat with desc = Econdor(scpat1, scpat2) }, fun_defs
  | Econdexp(e) ->
     let e, fun_defs = expression env fun_defs e in
     { scpat with desc = Econdexp(e) }, fun_defs
  | Econdpat(e, p) ->
     let e, fun_defs = expression env fun_defs e in
     { scpat with desc = Econdpat(e, p) }, fun_defs
  | Econdon(scpat, e) ->
     let scpat, fun_defs = scondpat env fun_defs scpat in
     let e, fun_defs = expression env fun_defs e in
     { scpat with desc = Econdon(scpat, e) }, fun_defs

and block env fun_defs ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list, fun_defs =
    Misc.map_fold (local env) fun_defs l_list in
  let eq_list, fun_defs =
    Misc.map_fold (equation env) fun_defs eq_list in
  { b with b_locals = l_list; b_body = eq_list }, fun_defs

(** Convert a value into an expression. *)
(* [exp_of_value fun_defs v = acc', e] where
 * - fun_defs is a set of global function declarations;
 * - v is a value;
 * - e is the corresponding expression for v *)
and exp_of_value fun_defs { value_exp = v; value_name = opt_name } =
  match opt_name with
  | Some(qualident) ->
     Zaux.emake (Zaux.global (Lident.Modname(qualident))) Deftypes.no_typ,
     fun_defs
  | None ->
     (* otherwise translate the value into an expression *)
     let desc, fun_defs =
       match v with
       | Vconst(i) -> Econst(i), fun_defs
       | Vconstr0(qualident) ->
	  Econstr0(Lident.Modname(qualident)), fun_defs
       | Vtuple(v_list) ->
	  let v_list, fun_defs =
	    Misc.map_fold exp_of_value fun_defs v_list in
	  Etuple(v_list), fun_defs
       | Vrecord(l_v_list) ->
	  let l_e_list, fun_defs =
	    Misc.map_fold
	      (fun fun_defs (qid, v) ->
	       let v, fun_defs = exp_of_value fun_defs v in
	       (Lident.Modname(qid), v), fun_defs)
	      fun_defs l_v_list in
	  Erecord(l_e_list), fun_defs
       | Vperiod(p) -> Eperiod(p), fun_defs
       | Vfun(funexp, env) ->
	  let funexp, fun_defs = lambda env fun_defs funexp in
	  (* introduce a new function *)
	  let name = fresh () in
	  Zaux.global (Lident.Name(name)),
	  { fundefs = (name, funexp) :: fun_defs.fundefs }
       | Vabstract(qualident) ->
	  Zaux.global (Lident.Modname(qualident)), fun_defs in
     Zaux.emake desc Deftypes.no_typ, fun_defs


(* Reduction under a function body. *)
and lambda env fun_defs ({ f_body = e } as funexp) =
  let e, fun_defs = expression env fun_defs e in
  { funexp with f_body = e }, fun_defs

(* The main function. Reduce every definition according to [Misc.red_list] *)
(* and [Misc.red_all]. This step may introduce extra function definitions *)
let implementation_list ff impl_list =
  let set_value_code name v =
    let ({ info = info } as entry) =
      try Modules.find_value (Lident.Name(name))
      with Not_found ->
	let qualname = Modules.qualify name in
	let info = Global.value_desc false Deftypes.no_typ_scheme qualname in
	Modules.add_value name info; { qualid = qualname; info = info } in
    Global.set_value_code entry v in

  (* convert a function declaration into an implementation phrase *)
  (* add every entry in the global symbol table once it has been typed *)
  let make (name, funexp) impl_defs =
    set_value_code name (value_code (Vfun(funexp, Env.empty)));
    Zaux.make (Efundecl(name, funexp)) :: impl_defs in

  (* [fun_defs] is the list of extra functions that have been introduced *)
  (* at the moment only function with no parameters are kept *)
  (* for later steps of the compiler *)
  let implementation impl_defs impl = 
    match impl.desc with
    | Econstdecl(f, e) ->
       (* a global value must be a constant *)
       let v = Static.expression Env.empty e in
       (* add [f \ v] in the global symbol table *)
       let v = Global.value_name (Modules.qualify f) v in
       set_value_code f v;
       let e, { fundefs = fun_defs } = exp_of_value empty v in
       { impl with desc = Econstdecl(f, e) } ::
	 List.fold_right make fun_defs impl_defs
    | Efundecl(f, funexp) ->
       (* if [f] is marked to be reduced, reduce it *)
       (* if flag -redall is true, reduce it only if it has no more static *)
       (* parameter *)
       let ({ info = { value_typ = tys } } as entry) =
	 try Modules.find_value (Lident.Name(f))
	 with Not_found -> assert false in
       let no_parameter = Types.noparameters tys in
       (* strong reduction (under the lambda) when [no_parameter] *)
       let funexp, impl_defs =
	 if no_parameter then
	   let funexp, { fundefs = fun_defs } = lambda Env.empty empty funexp in
	   funexp, { impl with desc = Efundecl(f, funexp) } ::
		     List.fold_right make fun_defs impl_defs
	 else funexp, impl_defs in
       let v = Global.value_code (Global.Vfun(funexp, Env.empty)) in
       let v = Global.value_name (Modules.qualify f) v in
       set_value_code f v;
       impl_defs
    | _ -> impl :: impl_defs in
  try
    let impl_list = List.fold_left implementation [] impl_list in
    List.rev impl_list
  with
  | TypeError ->
     Format.eprintf
       "@[Internal error (static reduction):@,\
        static evaluation failed because of a typing error.@.@]";
     raise Error
  | NotStatic(exp_or_eq) ->
     let print ff = function
       | Exp(e) -> Printer.expression ff e
       | Eq(eq) -> Printer.equation ff eq in
     Format.eprintf
       "@[%aInternal error (static reduction):@,\
        static evaluation failed because the expression is not static.@.@]"
       print exp_or_eq;
     raise Error

	   
