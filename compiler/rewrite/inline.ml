(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* static expansion of function calls (inlining) *)
(* input: source code *)
(* output: source code *)
(* inlining is done according to the following: *)
(* - calls to atomic functions are not inlined. *)
(* - function calls annotated with [inline] are systematically inlined *)
(* - small functions (according to a cost function) are statically expanded *)
(* we compute an estimated cost for every function definition [f x = e] *)
(* functions whose cost body is less than [inline + cost f(x)]  *)
(* are inlined *)
(* the cost depends on the number of parameters and the size of its body *)
(* the inlining function preserves typing, i.e., if e is well typed *)
(* (e itself and any of its subterms) e is inlined into e', then e' *)
(* is also well typed *)
open Misc
open Ident
open Lident
open Global
open Zelus
open Zaux
      
exception No_inline;;

inlining_level := -100000

(** Decide whether a global function has to be inlined or not *)
(** A function is inlined either because [is_inline = true] *)
(** or it is small enough *)
let inline is_inline lname =
  let { info = { value_code = { Global.value_exp = v };
		 value_typ = { Deftypes.typ_vars = l } } } = 
    Modules.find_value lname in
  match v with
  | Global.Vfun({ f_args = p_list; f_body = e } as body, _) ->
     if is_inline then body
     else if Cost.expression e (!inlining_level + List.length p_list) then body
     else raise No_inline
  | _ -> raise No_inline
    
(** Building an expression [let reset res = e every r in res] *)
let reset e e_reset =
  let res = Ident.fresh "r" in
  let eq = eqmake (EQreset([eqmake (EQeq(varpat res e.e_typ, e))], e_reset)) in
  let env = 
    Env.singleton res
		  { Deftypes.t_sort = Deftypes.value;
		    Deftypes.t_typ = e.e_typ } in
  { e with e_desc =
	     Elet({ l_rec = false; l_env = env; l_eq = [eq];
		    l_loc = Location.no_location }, var res e.e_typ) }

(** Build a renaming from an environment *)
let build env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  Env.fold buildrec env (Env.empty, Env.empty)

(** rename a variable *)
let rename x renaming =
  try Env.find x renaming
  with Not_found ->
    Misc.internal_error "Inline: unbound name" Printer.name x

(** Renaming of type expressions *)
let rec type_expression renaming ({ desc = desc } as ty_e) =
  match desc with
  | Etypevar _ -> ty_e
  | Etypeconstr(g, ty_list) ->
     { ty_e with desc =
		   Etypeconstr(g, List.map (type_expression renaming) ty_list) }
  | Etypetuple(ty_list) ->
     { ty_e with desc =
		   Etypetuple(List.map (type_expression renaming) ty_list) }
  | Etypevec(ty_vec, s) ->
     { ty_e with desc =
		   Etypevec(type_expression renaming ty_vec, size renaming s) }
  | Etypefun(k, opt_name, ty_arg, ty_res) ->
     let ty_arg = type_expression renaming ty_arg in
     let opt_name, renaming =
       match opt_name with
       | None -> opt_name, renaming
       | Some(n) ->
	  let m = Ident.fresh (Ident.source n) in
	  Some(m), Env.add n m renaming in
     let ty_res = type_expression renaming ty_res in
     { ty_e with desc = Etypefun(k, opt_name, ty_arg, ty_res) }

and size renaming ({ desc = desc } as s) =
  match desc with
  | Sconst _ | Sglobal _ -> s
  | Sname(n) -> { s with desc = Sname(rename n renaming) }
  | Sop(op, s1, s2) ->
      { s with desc = Sop(op, size renaming s1, size renaming s2) }

(** Rename an operator *)
let operator renaming op =
  match op with
  | Eunarypre | Efby | Eminusgreater | Eifthenelse
  | Eup | Etest | Edisc | Ehorizon | Einitial | Eaccess
  | Eupdate | Econcat | Eatomic -> op
  | Eslice(s1, s2) -> Eslice(size renaming s1, size renaming s2)
  		       
(** Renaming of patterns *)
let rec pattern renaming ({ p_desc = desc } as p) =
  match desc with
  | Ewildpat | Econstpat _ | Econstr0pat _ -> p
  | Evarpat(n) ->  { p with p_desc = Evarpat(rename n renaming) }
  | Econstr1pat(c, p_list) ->
      { p with p_desc = Econstr1pat(c, List.map (pattern renaming) p_list) }
  | Etuplepat(p_list) ->
      { p with p_desc = Etuplepat(List.map (pattern renaming) p_list) }
  | Erecordpat(n_p_list) ->
      { p with p_desc =
		 Erecordpat(List.map (fun (ln, p) -> (ln, pattern renaming p))
		n_p_list) }
  | Ealiaspat(p1, n) ->
      let n = rename n renaming in
      { p with p_desc = Ealiaspat(pattern renaming p1, n) }
  | Eorpat(p1, p2) ->
      { p with p_desc = Eorpat(pattern renaming p1, pattern renaming p2) }
  | Etypeconstraintpat(p1, ty) ->
      { p with p_desc = Etypeconstraintpat(pattern renaming p1,
					    type_expression renaming ty) }

	
(** Renaming of expressions *)
let rec expression renaming ({ e_desc = desc } as e) =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e
  | Elocal(n) -> { e with e_desc = Elocal(rename n renaming) }
  | Elast(n) -> { e with e_desc = Elast(rename n renaming) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression renaming) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (expression renaming) e_list) }
  | Erecord(n_e_list) -> 
     { e with e_desc =
		Erecord(List.map (fun (ln, e) -> (ln, expression renaming e)) 
				 n_e_list) }
  | Erecord_access(e_record, ln) ->
     { e with e_desc = Erecord_access(expression renaming e_record, ln) }
  | Erecord_with(e_record, n_e_list) -> 
     { e with e_desc =
		Erecord_with(expression renaming e_record,
			     List.map
			       (fun (ln, e) -> (ln, expression renaming e)) 
			       n_e_list) }
  | Eop(op, e_list) ->
     { e with e_desc = Eop(operator renaming op,
			   List.map (expression renaming) e_list) }
  | Eapp({ app_inline = i } as app,
	 ({ e_desc = Eglobal { lname = f } } as op), e_list) ->
     let e_list = List.map (expression renaming) e_list in
     begin try
         let { f_args = p_list; f_body = e; f_env = env } =
	   inline (!Misc.inline_all || i) f in
         letin renaming env p_list e_list e
       with
       | No_inline ->
          (* the body of [f] is not visible or the gain of the inlining *)
          (* threshold is not enough *)
          { e with e_desc = Eapp(app, op, e_list) }
     end
  | Eapp(app, e, e_list) ->
     { e with e_desc = 
		Eapp(app, expression renaming e,
		     List.map (expression renaming) e_list) }
  | Etypeconstraint(e1, ty) -> 
     { e with e_desc = Etypeconstraint(expression renaming e1, ty) }      
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(expression renaming e1, expression renaming e2) }
  | Eperiod { p_phase = p1; p_period = p2 } ->
     { e with e_desc = Eperiod { p_phase = Misc.optional_map (expression renaming) p1;
                                 p_period = expression renaming p2 } }
  | Elet(l, e_let) ->
     let renaming, l = local renaming l in
     { e with e_desc = Elet(l, expression renaming e_let) }
  | Eblock(b, e_block) ->
     let renaming, b = block renaming b in
     { e with e_desc = Eblock(b, expression renaming e_block) }
  | Epresent _ | Ematch _ -> assert false
				    
(** Renaming a local declaration *)
and local renaming ({ l_eq = eq_list; l_env = env } as l) =
    let env, renaming0 = build env in
    let renaming = Env.append renaming0 renaming in
    let eq_list = List.map (equation renaming) eq_list in
    renaming,
    { l with l_eq = eq_list; l_env = env }

and equation renaming ({ eq_desc = desc } as eq) =
  let desc = match desc with
    | EQeq(p, e) ->
       EQeq(pattern renaming p, expression renaming e)
    | EQpluseq(x, e) ->
       EQpluseq(rename x renaming, expression renaming e)
    | EQinit(x, e0) ->
          EQinit(rename x renaming, expression renaming e0)
    | EQnext(x, e, e0_opt) ->
       EQnext(rename x renaming, expression renaming e,
	      Misc.optional_map (expression renaming) e0_opt)
    | EQder(x, e, e0_opt, p_e_list) ->
       let body { p_cond = sc; p_body = e; p_env = env; p_zero = zero } =
	 let env, renaming0 = build env in
	 let renaming = Env.append renaming0 renaming in
	 { p_cond = scondpat renaming sc;
	   p_body = expression renaming e;
	   p_env = env;
	   p_zero = zero } in
       let e = expression renaming e in
       let e0_opt = Misc.optional_map (expression renaming) e0_opt in
       EQder(rename x renaming, e, e0_opt, List.map body p_e_list)
    | EQmatch(total, e, m_b_list) ->
       let body ({ m_pat = p; m_body = b; m_env = env } as m_h) =
         let env, renaming0 = build env in
         let renaming = Env.append renaming0 renaming in
         let _, b = block renaming b in
	 { m_h with m_pat = pattern renaming p;
		    m_body = b; m_env = env } in
       let e = expression renaming e in
       EQmatch(total, e, List.map body m_b_list)
    | EQreset(res_eq_list, e) ->
       EQreset(List.map (equation renaming) res_eq_list, expression renaming e)
    | EQand(and_eq_list) ->
       EQand(List.map (equation renaming) and_eq_list)
    | EQbefore(before_eq_list) ->
       EQbefore(List.map (equation renaming) before_eq_list)
    | EQpresent(p_h_list, b_opt) ->
       let body { p_cond = sc; p_body = b; p_env = env; p_zero = zero } =
         let env, renaming0 = build env in
         let renaming = Env.append renaming0 renaming in
         let _, b = block renaming b in
	 { p_cond = scondpat renaming sc;
           p_body = b; p_env = env; p_zero = zero } in
       let b_opt =
	 Misc.optional_map (fun b -> let _, b = block renaming b in b) b_opt in
       EQpresent(List.map body p_h_list, b_opt)
    | EQemit(x, e_opt) ->
       EQemit(rename x renaming, Misc.optional_map (expression renaming) e_opt)
    | EQblock(b) ->
       let _, b = block renaming b in EQblock(b)
    | EQautomaton(is_weak, s_h_list, se_opt) ->
       let build_state_names renaming { s_state = { desc = desc } } =
	 match desc with
	 | Estate0pat(n) | Estate1pat(n, _) ->
             let m = Ident.fresh (Ident.source n) in
             Env.add n m renaming in
       let statepat renaming ({ desc = desc } as spat) =
	 match desc with
	 | Estate0pat(x) -> { spat with desc = Estate0pat(rename x renaming) }
	 | Estate1pat(x, x_list) ->
	    let x = rename x renaming in
	    let x_list = List.map (fun x -> rename x renaming) x_list in
	    { spat with desc = Estate1pat(x, x_list) } in
       let state_exp renaming ({ desc = desc } as se) =
	 match desc with
	 | Estate0(x) -> { se with desc = Estate0(rename x renaming) }
	 | Estate1(x, e_list) ->
	    { se with desc =
			Estate1(rename x renaming,
				List.map (expression renaming) e_list) } in
       let escape renaming ({ e_cond = scpat; e_block = b_opt;
			      e_next_state = se; e_env = env } as esc) =
	 let env, renaming0 = build env in
	 let renaming = Env.append renaming0 renaming in
	 let renaming, b_opt =
	   match b_opt with
	   | None -> renaming, None
	   | Some(b) ->
	      let renaming, b = block renaming b in renaming, Some(b) in
	 { esc with e_cond = scondpat renaming scpat; 
		    e_block = b_opt;
		    e_next_state = state_exp renaming se;
		    e_env = env } in
       let body renaming
		({ s_state = spat; s_body = b; s_trans = esc_list;
		   s_env = env } as h) =
	 let env, renaming0 = build env in
	 let renaming = Env.append renaming0 renaming in
	 let spat = statepat renaming spat in
	 let renaming, b = block renaming b in
	 { h with s_state = spat;
		  s_body = b;
		  s_trans = List.map (escape renaming) esc_list;
		  s_env = env } in
       let renaming =
	 List.fold_left build_state_names renaming s_h_list in
       let se_opt = Misc.optional_map (state_exp renaming) se_opt in
       EQautomaton(is_weak, List.map (body renaming) s_h_list, se_opt)
    | EQforall({ for_index = i_list; for_init = init_list;
		 for_body = b_eq_list;
		 for_in_env = in_env; for_out_env = out_env } as f_body) ->
       let in_env, renaming0 = build in_env in
       let out_env, renaming1 = build out_env in
       let renaming = Env.append renaming0 (Env.append renaming1 renaming) in
       let index ({ desc = desc } as ind) =
	 let desc = match desc with
	   | Einput(x, e) -> Einput(rename x renaming,
				    expression renaming e)
	   | Eoutput(x, xout) -> Eoutput(rename x renaming,
					 rename xout renaming)
	   | Eindex(x, e1, e2) -> Eindex(rename x renaming,
					 expression renaming e1,
					 expression renaming e2) in
	 { ind with desc = desc } in
       let init ({ desc = desc } as ini) =
	 let desc = match desc with
	   | Einit_last(x, e) -> Einit_last(rename x renaming,
					    expression renaming e) in
	 { ini with desc = desc } in
       let _, b_eq_list = block renaming b_eq_list in
       EQforall { f_body with
                  for_index = List.map index i_list;
		  for_init = List.map init init_list;
		  for_body = b_eq_list;
		  for_in_env = in_env; for_out_env = out_env } in
      { eq with eq_desc = desc; eq_write = Deftypes.empty }
      
and scondpat renaming ({ desc = desc } as sc) =
  match desc with
    | Econdand(sc1, sc2) ->
        { sc with desc = 
	    Econdand(scondpat renaming sc1, scondpat renaming sc2) }
    | Econdor(sc1, sc2) ->
        { sc with desc = Econdor(scondpat renaming sc1, scondpat renaming sc2) }
    | Econdexp(e) ->
        { sc with desc = Econdexp(expression renaming e) }
    | Econdon(sc1, e) ->
        { sc with desc = 
	    Econdon(scondpat renaming sc1, expression renaming e) }
    | Econdpat(e, p) ->
        { sc with desc = Econdpat(expression renaming e, pattern renaming p) }

and vardec renaming ({ vardec_name = n } as v) =
    { v with vardec_name = rename n renaming }
  
and block renaming 
    ({ b_vars = n_list; b_locals = l_list; b_body = eq_list; 
       b_env = n_env } as b) =
  let rec local_list renaming l_list =
    match l_list with
    | [] -> renaming, []
    | l :: l_list ->
       let renaming, l = local renaming l in
       let renaming, l_list = local_list renaming l_list in
       renaming, l :: l_list in
  
  let n_env, renaming0 = build n_env in
  let renaming = Env.append renaming0 renaming in
  let n_list = List.map (vardec renaming) n_list in
  let renaming_l, l_list = local_list renaming l_list in
  renaming_l,
  { b with b_vars = n_list; b_locals = l_list; 
    b_body = List.map (equation renaming_l) eq_list; 
    b_write = Deftypes.empty;
    b_env = n_env }

(* returns [let p1' = e1 and ... and pn' = en in e[p1'/p1,...,p'n/pn] *)
(* in which [p1,...,pn] are renamed into [p1',...,pn'] and [e] is *)
(* recursively inlined *)
and letin renaming env p_list e_list e =
  let eqmake p e = eqmake (EQeq(p, e)) in

  let env, renaming0 = build env in
  let renaming = Env.append renaming0 renaming in
  let p_list = List.map (pattern renaming) p_list in
  { e with e_desc =
      Elet({ l_rec = false; l_env = env; l_eq = List.map2 eqmake p_list e_list;
             l_loc = Location.no_location }, expression renaming e) }

let implementation acc impl = 
  match impl.desc with
    | Econstdecl(f, is_static, e) ->
       let e = expression Env.empty e in
       { impl with desc = Econstdecl(f, is_static, e) } :: acc
    | Efundecl(f, ({ f_args = p_list; f_body = e; f_env = f_env } as body)) ->
       let f_env, renaming = build f_env in
       let p_list = List.map (pattern renaming) p_list in
       let e = expression renaming e in
       let body = { body with f_args = p_list; f_body = e; f_env = f_env } in
       { impl with desc = Efundecl(f, body) } :: acc
    | _ -> impl :: acc
        
let implementation_list impl_list = Misc.fold implementation impl_list
