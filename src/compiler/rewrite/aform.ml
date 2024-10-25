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

(* A-normal form: distribution of tuples *)
(* for any variable [x: t1 *...* t2n, introduce fresh names *)
(* [x1:t1,...,xn:tn] so that [x = (x1,...,xn)] *)
(* distribute pattern matchings [(p1,...,pn) = (e1,...,en)] into *)
(* p1 = e1 and ... pn = en] *)
open Ident
open Zelus
open Deftypes
       
(* the type of the accumulator *)
type acc =
  { renaming: Ident.t Env.t; (* renaming environment *)
    env: (Typinfo.pattern * Typinfo.exp) Env.t;
  }
  
(* Build a renaming from an environment *)
let build global_funs ({ renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }

(* associate a pattern and an expression to a variable according to its type *)
(* [intro t_env subst = subst', t_env'] *)
let build global_funs ({ renaming; env } as acc) env =
  (* returns a pair [spat, se] with [spat] a pattern, [se] an expression *)
  let result { source } entry acc ty =
    let id = Ident.fresh source in
    (Aux.varpat id, Aux.var id),
    Env.add id { entry with t_tys = Deftypes.scheme ty } acc in
  let rec value id entry acc ({ t_desc } as ty) =
    match t_desc with
    | Tvar | Tarrow _ | Tvec _ | Tconstr _ -> result id entry acc ty
    | Tproduct(ty_list) ->
       let p_e_list, acc = Util.mapfold (value id entry) acc ty_list in
       let p_list, e_list = List.split p_e_list in
       (Aux.tuplepat p_list, Aux.tuple e_list), acc
    | Tlink(ty_link) -> value id entry acc ty_link in
  let add id ({ t_tys = { typ_body }; t_sort; t_path } as entry)
        (subst_acc, env_acc) =
    match t_sort with
    | Sort_val | Sort_var ->
	let r, env_acc = value id entry env_acc typ_body in
	Env.add id r subst_acc, env_acc
    | _ ->
     (* state variables are not splitted but renamed *)
     let r, env_acc = result id entry env_acc typ_body in
     Env.add id r subst_acc, env_acc in
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }Env.fold add t_env (subst, Env.empty)

(* matching. Translate [(p1,...,pn) = (e1,...,en)] into the set of *)
(* equations [p1 = e1 and ... and pn = en] *)
(* [compose] defines the type of equation: [init p = e] or [p = e] *)
let rec matching compose eq_list ({ pat_desc } as p) ({ e_desc } as e) =
  match pat_desc, e_desc with
    | Etuplepat(p_list), Etuple(e_list) ->
        matching_list compose eq_list p_list e_list
    | _ -> (compose p e) :: eq_list

and matching_list compose eq_list p_list e_list =
  List.fold_left2 (matching compose) eq_list p_list e_list

(* Functions which traverse the ast *)
(** expressions *)
let rec expression subst ({ e_desc = desc } as e) =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e
  | Elast(x) -> { e with e_desc = Elast(name_of_name x subst) }
  | Elocal(x) ->
     let ename = exp_of_name x subst in 
     { e with e_desc = ename.e_desc }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression subst) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (expression subst) e_list) }
  | Erecord(n_e_list) -> 
     { e with e_desc =
		Erecord(List.map (fun (ln, e) ->
				  (ln, expression subst e)) n_e_list) }
  | Erecord_access(e_record, ln) ->
     { e with e_desc = Erecord_access(expression subst e_record, ln) }
  | Erecord_with(e_record, n_e_list) -> 
     { e with e_desc =
		Erecord_with(expression subst e_record,
			     List.map (fun (ln, e) ->
				       (ln, expression subst e)) n_e_list) }
  | Eop(op, e_list) ->
     { e with e_desc = Eop(op, List.map (expression subst) e_list) }
  | Eapp(app, e_op, e_list) ->
     let e_op = expression subst e_op in
     let e_list = List.map (expression subst) e_list in
     { e with e_desc = Eapp(app, e_op, e_list) }
  | Etypeconstraint(e1, ty) -> 
     { e with e_desc = Etypeconstraint(expression subst e1, ty) }      
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(expression subst e1, expression subst e2) }
  | Elet(l, e_let) ->
     let subst, l = local subst l in
     { e with e_desc = Elet(l, expression subst e_let) }
  | Eperiod _ | Epresent _ | Ematch _ | Eblock _ -> assert false

(** Local declarations *)
and local subst ({ l_eq = eq_list; l_env = l_env } as l) =
  let subst, l_env = build l_env subst in
  let eq_list = equation_list subst eq_list in
  subst, { l with l_eq = eq_list; l_env = l_env }

and pattern subst p =
  match p.p_desc with
  | Ewildpat | Econstpat _ | Econstr0pat _ -> p
  | Etuplepat(p_list) -> 
      { p with p_desc = Etuplepat(List.map (pattern subst) p_list) }
  | Econstr1pat(c, p_list) -> 
      { p with p_desc = Econstr1pat(c, List.map (pattern subst) p_list) }
  | Evarpat(x) ->
     let pname = pat_of_name x subst in     
     { p with p_desc = pname.p_desc }
  | Ealiaspat(p1, n) ->
      { p with p_desc = Ealiaspat(pattern subst p1, name_of_name n subst) }
  | Eorpat(p1, p2) ->
      { p with p_desc = Eorpat(pattern subst p1, pattern subst p2) }
  | Erecordpat(l_p_list) ->
      let l_p_list = 
        List.map (fun (l, p) -> (l, pattern subst p)) l_p_list in
      { p with p_desc = Erecordpat(l_p_list) }
  | Etypeconstraintpat(p1, ty) ->
      { p with p_desc = Etypeconstraintpat(pattern subst p1, ty) }

and equation subst eq_list ({ eq_desc = desc } as eq) =
  let returns eq eq_desc eq_list =
    { eq with eq_desc = eq_desc; eq_write = Deftypes.empty } :: eq_list in
  match desc with
  | EQeq(p, e) -> 
     let p = pattern subst p in
     let e = expression subst e in
     matching (fun p e -> Zaux.eqmake (EQeq(p, e))) eq_list p e
  | EQder(x, e, e_opt, []) ->
     returns eq (EQder(name_of_name x subst, expression subst e,
		       Zmisc.optional_map (expression subst) e_opt, [])) eq_list
  | EQinit(x, e) ->
     (* [x] should not be renamed as it is a state variable *)
     returns eq (EQinit(name_of_name x subst,
			expression subst e)) eq_list
  | EQnext(x, e, e_opt) ->
     (* [x] should not be renamed as it is a state variable *)
     returns eq (EQnext(name_of_name x subst, expression subst e,
			Zmisc.optional_map (expression subst) e_opt)) eq_list
  | EQpluseq(x, e) ->
     (* [x] should not be renamed as it is a multi-write variable *)
     returns eq (EQpluseq(name_of_name x subst,
			  expression subst e)) eq_list
  | EQreset(reset_eq_list, e) ->
     returns eq (EQreset(equation_list subst reset_eq_list,
			 expression subst e)) eq_list
  | EQmatch(total, e, m_h_list) ->
     returns eq (EQmatch(total, expression subst e, 
			 List.map (handler subst) m_h_list)) eq_list
  | EQblock(b) ->
     returns eq (EQblock(block subst b)) eq_list
  | EQand(and_eq_list) ->
     returns eq (EQand(equation_list subst and_eq_list)) eq_list
  | EQbefore(before_eq_list) ->
     returns eq (EQbefore(equation_list subst before_eq_list)) eq_list
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list;
		for_in_env = fi_env; for_out_env = fo_env } as b) ->
     let subst, fi_env = build fi_env subst in
     let subst, fo_env = build fo_env subst in
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(i, e) -> Einput(name_of_name i subst, expression subst e)
	 | Eoutput(oi, o) ->
	    Eoutput(name_of_name oi subst, name_of_name o subst)
	 | Eindex(i, e1, e2) ->
	    Eindex(name_of_name i subst,
		   expression subst e1, expression subst e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(i, e) ->
	    Einit_last(name_of_name i subst, expression subst e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block subst b_eq_list in
     returns eq
	     (EQforall
		{ b with for_index = i_list; for_init = init_list;
			 for_body = b_eq_list; for_in_env = fi_env;
			 for_out_env = fo_env }) eq_list
  | EQautomaton _ | EQpresent _ | EQder _ | EQemit _ -> assert false
							       
and equation_list subst eq_list =
  let eq_list = List.fold_left (equation subst) [] eq_list in List.rev eq_list

and handler subst ({ m_pat = p; m_body = b; m_env = m_env } as m_h) =
  let subst, m_env = build m_env subst in
  let p = pattern subst p in
  { m_h with m_pat = p; m_body = block subst b; m_env = m_env }

     
and block subst ({ b_vars = v_list; b_body = eq_list; b_env = b_env } as b) =
  (* the field [b.b_locals] must be [] as this compilation step is done *)
  (* after normalisation *)
  let vardec_list subst v_list =
  (* Warning. if [n] is a state variable or associated with a *)
  (* default value of combine function, it is not split into a tuple *)
  (* but a single name. The code below makes this assumption. *)
  let vardec acc ({ vardec_name = n} as v) =
    let p = pat_of_name n subst in
    let nset = Vars.fv_pat S.empty S.empty p in
    S.fold (fun n acc -> { v with vardec_name = n } :: acc) nset acc in
  List.fold_left vardec [] v_list in
  
 let subst, b_env = build b_env subst in
  let v_list = vardec_list subst v_list in
  { b with b_vars = v_list; b_body = equation_list subst eq_list;
	   b_env = b_env; b_write = Deftypes.empty }

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> impl
    | Econstdecl(n, is_static, e) ->
       { impl with desc = Econstdecl(n, is_static, expression Env.empty e) }
    | Efundecl(n, ({ f_body = e; f_env = f_env; f_args = p_list } as body)) ->
       let subst, f_env = build f_env Env.empty in
       let p_list = List.map (pattern subst) p_list in
       let e = expression subst e in
       { impl with desc =
		     Efundecl(n, { body with f_body = e;
					     f_env = f_env; f_args = p_list }) }

let implementation_list impl_list = Zmisc.iter implementation impl_list

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with
      expression; global_funs; set_index; get_index; implementation; 
      open_t } in
  let p, _ = Mapfold.program_it funs { empty with genv } p in
  p

