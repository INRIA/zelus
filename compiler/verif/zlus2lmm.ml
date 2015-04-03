(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* Translation into Lustre-- *)

(* no automaton, no present *)

(* Tr(ck)(match e with
          | p1 -> E1 | ... | pn -> En) = 

   with one defined variable y (defnames = {y}) and used variable x
   (example: E1 = local t in do t = x + 3 and y = t + 2 done)

becomes:
 
   local c in
   do
     c = Tr(ck)(e)
   and
     Tr(c on c1)(E1)[y_1/y]
   and
     ...
   and
     Tr(c on cn)(En)[y_n/y]
   and
     c1 = test(p1)(c) and ... and cn = test(pn)(c)
   and
     pat(p1) = c and ... and pat(pn) = c
   and
     y = if c1 then y_1 else ... if cn then y_n [else pre y]

where:

  test(p)(c) returns an expression testing that the pattern p matches c

  pat(p) returns a pattern with variables only

Tr(ck)(x = e) = x = if ck then Tr(ck)(e) else pre x

                with the special case that if base then e else e' = e

*)

   
open Location
open Ident
open Zelus
open Deftypes

let eq_make pat e = 
  { Lmm.eq_lhs = pat; Lmm.eq_rhs = e; Lmm.eq_loc = no_location }
    
let make desc = { Lmm.e_desc = desc;
		  Lmm.e_typ = Deftypes.no_typ;
		  Lmm.e_loc = no_location }
		  
let e_true = make (Lmm.Econst(Ebool(true)))
let e_false = make (Lmm.Econst(Ebool(false)))
		   
let bool_op op e1 e2 =
  make (Lmm.Eapp(Lmm.Eop(Lident.Modname(Initial.pervasives_name op)),
		 [e1; e2]))
       
let equal_op e1 e2 = bool_op "=" e1 e2
let and_op e1 e2 = bool_op "&&" e1 e2
let or_op e1 e2 = bool_op "||" e1 e2
			  
type ck = | Ck_base | Ck_on of ck * Lmm.exp
				      
let on ck c = Ck_on(ck, make (Lmm.Elocal(c)))
		   
(* from a clock to a boolean expression *)
let rec clock = function
  | Ck_base -> e_true
  | Ck_on(Ck_base, e) -> e
  | Ck_on(ck, e) -> and_op (clock ck) e
			   
(* for a pair [pat, e] computes the equation [pat_v = e] and boolean *)
(* condition c where [pat_v] is only made of variables and [c] *)
(* is true when [pat] matches [e] *)
let rec filter eqs { p_desc = p_desc } e =
  match p_desc with
  | Ewildpat ->  eqs, e_true
  | Evarpat(id) -> (eq_make (Lmm.Evarpat(id)) e) :: eqs, e_true
  | Econstpat(c) -> eqs, equal_op (make (Lmm.Econst(c))) e
  | Econstr0pat(c) -> eqs, equal_op (make (Lmm.Econstr0(c))) e
  | Etuplepat(p_list) ->
     (* introduce n fresh names *)
     let n_list = List.map (fun _ -> Ident.fresh "") p_list in
     let eqs, cond =
       List.fold_left2
	 (fun (eqs, cond) p n ->
	  let eqs, cond_p_n = filter eqs p (make (Lmm.Elocal(n))) in
	  eqs, and_op cond cond_p_n) (eqs, e_true) p_list n_list in
     eqs, cond
  | Ealiaspat(p, id) ->
     let eqs, cond = filter eqs p e in
     (eq_make (Lmm.Evarpat(id)) e) :: eqs, cond
  | Etypeconstraintpat(p, _) -> filter eqs p e
  | Eorpat(p1, p2) ->
     let eqs, cond1 = filter eqs p1 e in
     let eqs, cond2 = filter eqs p2 e in
     eqs, or_op cond1 cond2
  | Erecordpat(l_p_list) ->
     let eqs, cond =
       List.fold_left
	 (fun (eqs, cond) (l, p) ->
	  let eqs, cond_l_p = filter eqs p (make (Lmm.Erecord_access(e, l))) in
	  eqs, and_op cond cond_l_p) (eqs, e_true) l_p_list in
     eqs, cond
	    
(* translate an operator *)
let operator ck op e_list =
  match op with
  | Eunarypre -> Lmm.Eapp(Lmm.Eunarypre, e_list)
  | Eifthenelse -> Lmm.Eapp(Lmm.Eifthenelse, e_list) 
  | Eminusgreater -> Lmm.Eapp(Lmm.Eminusgreater, e_list)
  | Eop(_, lid) | Eevery(_, lid) ->
		   if Types.is_a_function lid then Lmm.Eapp(Lmm.Eop(lid), e_list)
		   else Lmm.Eapp(Lmm.Eop(lid), e_false :: (clock ck) :: e_list)
  | Efby | Eup | Einitial | Edisc
  | Etest -> assert false
		    
(* renaming of a name by an other *)
let rename x subst =
  try Env.find x subst
  with | Not_found -> assert false
			     
(* [subst] is a substitution to rename [last x] by a fresh variable [lx] *)
let rec expression ck subst { e_desc = desc } =
  match desc with
  | Elocal(id) -> make (Lmm.Elocal(id))
  | Eglobal(lid) -> make (Lmm.Eglobal(lid))
  | Econst(im) -> make (Lmm.Econst(im))
  | Econstr0(lid) -> make (Lmm.Econstr0(lid))
  | Elast(lx) -> make (Lmm.Elocal(rename lx subst))
  | Eapp(op, e_list) ->
     make (operator ck op (List.map (expression ck subst) e_list))
  | Etuple(e_list) ->
     make (Lmm.Etuple(List.map (expression ck subst) e_list))
  | Erecord_access(e, lid) ->
     make (Lmm.Erecord_access(expression ck subst e, lid))
  | Erecord(l_e_list) ->
     make (Lmm.Erecord
	     (List.map (fun (l, e) -> (l, expression ck subst e)) l_e_list))
  | Etypeconstraint(e, _) -> expression ck subst e
  | Epresent _ | Ematch _ | Elet _ | Eseq _ | Eperiod _ -> assert false
								  
(* the set of shared variables from a set of defined names *)
let shared_variables { dv = dv } = dv
				     
(* returns the expression associated to [x] in a substitution [name_to_exp] *)
(* if [x] is unbound, returns [pre x] *)
let get x name_to_exp =
  try
    Env.find x name_to_exp
  with
  | Not_found -> make (Lmm.Eapp(Lmm.Eunarypre, [make (Lmm.Elocal(x))]))
		      
(* [split s_set eqs = [eqs_acc, name_to_exp] splits eqs into *)
(* two complementary sets of equations *)
(* [name_to_exp] associates an expression to any names from [s_set] *)
let split s_set eqs =
  let split (eqs_acc, name_to_exp) ( { Lmm.eq_lhs = p; Lmm.eq_rhs = e } as eq) =
    match p with
    | Lmm.Evarpat(id) ->
       if S.mem id s_set then eqs_acc, Env.add id e name_to_exp
       else eq :: eqs_acc, name_to_exp
    | _ -> eq :: eqs_acc, name_to_exp in
  List.fold_left split ([], Env.empty) eqs
		 
(* [equation ck eq = eq_list] *)
let rec equation ck subst eqs { eq_desc = desc; eq_write = defnames } = 
  match desc with
  | EQeq({ p_desc = Evarpat(id) }, e) ->
     (eq_make (Lmm.Evarpat(id)) (expression ck subst e)) :: eqs
  | EQeq(p, e) ->
     let n = Ident.fresh "" in
     let eqs, _ = filter eqs p (make (Lmm.Elocal(n))) in
     (eq_make (Lmm.Evarpat(n)) (expression ck subst e)) :: eqs
  | EQmatch(total, e, p_h_list) ->
     (* first translate [e] *)
     let e = expression ck subst e in
     (* then compute the set of shared variables *)
     let s_set = shared_variables defnames in
     (* introduce [n] fresh clock names [c1,..., cn] *)
     let c_list =
       List.map (fun _ -> Ident.fresh "") p_h_list in
     
     (* translate the list of body *)
     let equations_from_handler eqs c { m_body = b } =
       let eqs = block (on ck c) subst eqs b in
       let eqs, name_to_exp = split s_set eqs in
       eqs, name_to_exp in
     
     let eqs, cond_name_to_exp_list =
       List.fold_right2
	 (fun c p_h (eqs, cond_name_to_exp_list) ->
	  let eqs, name_to_exp = equations_from_handler eqs c p_h in
	  eqs, (c, name_to_exp) :: cond_name_to_exp_list)
	 c_list p_h_list (eqs, []) in
     
     (* translate the list of patterns *)
     let patterns_from_handler eqs c { m_pat = p } =
       let eqs, cond = filter eqs p e in
       (eq_make (Lmm.Evarpat(c)) cond) :: eqs in
     let eqs = List.fold_left2 patterns_from_handler eqs c_list p_h_list in
     
     (* merge results for every shared variable. Returns *)
     (* if c1 then e1 else ... en *)
     let rec merge x cond_name_to_exp_list =
       match cond_name_to_exp_list with
       | [] -> assert false
       | [cond, name_to_exp] -> get x name_to_exp
       | (cond, name_to_exp) :: cond_name_to_exp_list ->
	  make (Lmm.Eapp(Lmm.Eifthenelse,
			 [make (Lmm.Elocal(cond)); get x name_to_exp;
			  merge x cond_name_to_exp_list])) in
     let eqs =
       S.fold
	 (fun x eqs ->
	  (eq_make (Lmm.Evarpat(x)) (merge x cond_name_to_exp_list)) :: eqs)
	 s_set eqs in
     eqs
  | EQinit(x, e) ->
     (eq_make (Lmm.Evarpat(rename x subst)) (expression ck subst e)) :: eqs
  | EQnext _ | EQset _ | EQblock _ | EQemit _ | EQautomaton _
  | EQpresent _ | EQder _ | EQreset _ -> assert false
									   
and equation_list ck subst eqs eq_list =
  List.fold_left (equation ck subst) eqs eq_list
 
and block ck subst eqs ({ b_body = body_eq_list; b_env = n_env } as b) =
  equation_list ck subst eqs body_eq_list
								     
let implementation impl_list impl =
  match impl.desc with
  | Eopen _ -> impl_list
  | Etypedecl(ty_decl) -> impl_list
  | Econstdecl(x, e) ->
     { Lmm.desc = Lmm.Econstdecl(x, expression Ck_base Env.empty e);
       Lmm.loc = no_location }
  | Efundecl(n, { f_kind = k; f_args = p_list; f_body = e }) ->
     let n_arg_list = List.map (fun _ -> Ident.fresh "") p_list in
     let e_list = List.map (fun n -> make (Elocal(n))) n_arg_list in
     let eqs, _ = List.fold_left2 filter [] p_list e_list in
     let arg_list =
       List.map2 (fun n pat -> { p_kind = Evar; p_name = n;
				 p_typ = pat.p_typ;
				 p_loc = no_location }) n_arg_list p_list in
     let n_output = Ident.fresh "" in
     let output = { p_kind = Evar; p_name = n_output;
		    p_typ = e.e_typ; p_loc = no_location } in
     let eqs = equation Ck_true subst eqs e in
     { Lmm.desc =
	 Lmm.Efundecl(n, { f_kind = k; f_inputs = arg_list; f_outputs = [output];
			   f_local = []; f_body = eqs; f_assert = None });
       Lmm.loc = no_location }
       
let implementation_list impl_list =
  List.rev (List.fold_left implementation [] impl_list)
