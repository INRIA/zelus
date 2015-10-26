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
(* static expansion of function calls (inlining) *)
(* input: any source code *)
(* output: any source code *)
(* inlining is done according to the following: *)
(* - calls to atomic functions are not inlined. *)
(* - function calls annotated with [inline] are systematically inlined *)
(* - small functions (according to a cost function) are statically expanded *)
(* we compute an estimated cost for every function definition [f x = e] *)
(* functions whose cost body is less than [inline + cost f(x)]  *)
(* are inlined *)
(* the cost depends on the number of parameters and the size of its body *)

open Misc
open Ident
open Lident
open Global
open Zelus
open Zaux
open Deftypes
     
exception No_inline;;

inlining_level := -100000

(** Simple cost function for an expression *)
(** [max] is the maximum allowed cost of [e] *)
(** raise Exit if the cost is greater than [max]      *)
(** continuous operators (up/der) reduce the local cost *)
(** since calling a function with continuous state need extra copy code *)
let cost_less e max =
  let c = ref 0 in
  let incr n =
    let c' = !c + n in
      if c' >= max then raise Exit
      else c := !c + n in
  let rec cost e =
    match e.e_desc with
      | Elocal _ | Elast _ | Econst _ | Econstr0 _ | Eglobal _ -> ()
      | Eapp(op, e_list) ->
          incr (1 + List.length e_list);
	  List.iter cost e_list; incr (cost_op op)
      | Etuple(e_list) -> incr 1; List.iter cost e_list
      | Erecord(n_e_list) ->
	 incr 1; List.iter (fun (label, e) -> cost e) n_e_list
      | Erecord_access(e, _) -> cost e
      | Eseq(e1, e2) -> cost e1; cost e2
      | Eperiod({ p_phase = p1_opt; p_period = p2 }) -> 
          incr (match p1_opt with | None -> 1 | Some _ -> 2)
      | Etypeconstraint(e, _) -> cost e
      | Elet(local, e_let) ->
          cost_local local; cost e_let
      | Epresent _ | Ematch _ -> assert false
  and cost_op op = 
    match op with 
      | Efby | Eunarypre | Eminusgreater -> 2
      | Edisc -> 4
      | Einitial -> 2
      | Eup -> -2
      | Eifthenelse | Etest | Eop _ | Eevery _ -> 1
      | Eafter -> 0
      | Ehorizon -> 1
  and cost_block { b_locals = l_list; b_body = eq_list } =
    List.iter cost_local l_list; List.iter cost_eq eq_list
  and cost_local { l_eq = eq_list } =
    List.iter cost_eq eq_list
  and cost_eq eq =
    match eq.eq_desc with
      | EQeq(_, e) | EQinit(_, e) | EQpluseq(_, e) -> incr 1; cost e
      | EQnext(_, e0, e_opt) -> 
	  incr 1; cost e0; Misc.optional_unit (fun _ e -> cost e) () e_opt
      | EQmatch(_, e, p_h_list) ->
          cost e;
          List.iter (fun { m_body = b } -> cost_block b) p_h_list
      | EQder(n, e, e0_opt, h) ->
          incr (-2);
          Misc.optional_unit (fun _ e -> cost e) () e0_opt;
          List.iter (fun { p_body = e } -> cost e) h;
          cost e
      | EQreset(eq_list, e) -> incr 1; List.iter cost_eq eq_list
      | EQpresent(p_h_list, b_opt) ->
	  List.iter (fun { p_body = b } -> cost_block b) p_h_list;
	  Misc.optional_unit (fun _ b -> cost_block b) () b_opt
      | EQemit(_, e_opt) ->
	  Misc.optional_unit (fun _ e -> cost e) () e_opt
      | EQblock(b) -> cost_block b
      | EQautomaton(_, s_h_list, se_opt) ->
	 List.iter cost_state_handler s_h_list;
	 Misc.optional_unit (fun _ se -> cost_state_exp se) () se_opt	 
  and cost_state_handler { s_body = b; s_trans = esc_list } =
    cost_block b; List.iter cost_escape esc_list
  and cost_escape { e_cond = scpat; e_block = b_opt; e_next_state = se } =
    cost_scpat scpat;
    Misc.optional_unit (fun _ b -> cost_block b) () b_opt;
    cost_state_exp se
  and cost_state_exp { desc = desc } =
    match desc with
    | Estate0 _ -> incr 1
    | Estate1(_, e_list) -> List.iter cost e_list
  and cost_scpat { desc = desc } =
    match desc with
    | Econdand(scpat1, scpat2)
    | Econdor(scpat1, scpat2) -> cost_scpat scpat1; cost_scpat scpat2
    | Econdexp(e) | Econdpat(e, _) -> cost e
    | Econdon(scpat, e) -> cost_scpat scpat; cost e
    
  in
  try
    cost e; true
  with
    | Exit -> false

(** Decide whether a global function has to be inlined or not *)
(** A function is inlined either because [is_inline = true] *)
(** or it is small enough and it is not atomic *)
let inline is_inline lname =
  let { info = { value_atomic = is_atomic;
		 value_code = opt_code; 
		 value_typ = { Deftypes.typ_vars = l } } } = 
    Modules.find_value lname in
  match opt_code with
    | Some({ f_args = p_list; f_body = e } as body) ->
       if is_atomic then raise No_inline
       else if is_inline then body
       else if cost_less e (!inlining_level + List.length p_list) then body
       else raise No_inline
    | _ -> raise No_inline
    
(* store the pre-compiled code into the environment for further use *)
let store f body = Global.set_code (Modules.find_value (Lident.Name(f))) body
    

(** Building a [let p1 = e1 and ... and pn = en in e] *)
let letin env p_list e_list e =
  let eqmake p e = eqmake (EQeq(p, e)) in
  { e with e_desc =
      Elet({ l_env = env;
             l_eq = List.map2 eqmake p_list e_list;
             l_loc = Location.no_location }, e) }

(** Building an expression [let reset res = e every r in res] *)
let reset e e_reset =
  let res = Ident.fresh "r" in
  let eq = eqmake (EQreset([eqmake (EQeq(varpat res e.e_typ, e))], e_reset)) in
  let env = 
    Env.singleton res
		  { Deftypes.t_sort = Deftypes.value; Deftypes.t_typ = e.e_typ } in
  { e with e_desc =
	     Elet({ l_env = env; l_eq = [eq];
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

(** Renaming of patterns *)
let rec pattern renaming ({ p_desc = desc } as p) =
  match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> p
    | Evarpat(n) ->  { p with p_desc = Evarpat(rename n renaming) }
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
        { p with p_desc = Etypeconstraintpat(pattern renaming p1, ty) }
        
(** Renaming of expressions *)
let rec expression renaming ({ e_desc = desc } as e) =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e
  | Elocal(n) -> { e with e_desc = Elocal(rename n renaming) }
  | Elast(n) -> { e with e_desc = Elast(rename n renaming) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression renaming) e_list) }
  | Erecord(n_e_list) -> 
     { e with e_desc =
		Erecord(List.map (fun (ln, e) -> (ln, expression renaming e)) 
				 n_e_list) }
  | Erecord_access(e, ln) ->
     { e with e_desc = Erecord_access(expression renaming e, ln) }
  | Eapp(Eop(is_inline, f), e_list) ->
     let e_list = List.map (expression renaming) e_list in
     begin try
         let { f_args = p_list; f_body = e; f_env = env } = inline is_inline f in
         let env, renaming0 = build env in
         let renaming = Env.append renaming0 renaming in
         letin env (List.map (pattern renaming) p_list) e_list
               (expression renaming e)
       with
       | No_inline ->
          (* the body of [f] is not visible or the gain of the inlining *)
          (* threshold is not enough *)
          { e with e_desc = Eapp(Eop(is_inline, f), e_list) }
     end
  | Eapp(Eevery(is_inline, f), e_reset :: e_list) ->
     let e_reset = expression renaming e_reset in
     let e_list = List.map (expression renaming) e_list in
     begin try
         let { f_args = p_list; f_body = e; f_env = env } = inline is_inline f in
         let env, renaming0 = build env in
         let renaming = Env.append renaming0 renaming in
         letin env (List.map (pattern renaming) p_list) e_list
               (reset (expression renaming e) e_reset)
       with
       | No_inline ->
          (* the body of [f] is not visible or the gain of the inlining *)
          (* threshold is not enough *)
          { e with e_desc = Eapp(Eevery(is_inline, f), e_reset :: e_list) }
     end
  | Eapp(op, e_list) ->
     { e with e_desc = 
		Eapp(op, List.map (expression renaming) e_list) }
  | Etypeconstraint(e1, ty) -> 
     { e with e_desc = Etypeconstraint(expression renaming e1, ty) }      
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(expression renaming e1, expression renaming e2) }
  | Eperiod _ -> e
  | Elet(l, e_let) ->
     let renaming, l = local renaming l in
     { e with e_desc = Elet(l, expression renaming e_let) }
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
    | EQreset(eq_list, e) ->
       EQreset(List.map (equation renaming) eq_list, expression renaming e)
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
       EQautomaton(is_weak, List.map (body renaming) s_h_list, se_opt) in
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


and block renaming 
    ({ b_vars = n_list; b_locals = l_list; b_body = eq_list; 
       b_write = { dv = dv; di = di; der = der }; b_env = n_env } as b) =
  let vardec renaming ({ vardec_name = n } as v) =
    { v with vardec_name = rename n renaming } in
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

let implementation acc impl = 
  match impl.desc with
    | Econstdecl(f, e) ->
       let e = expression Env.empty e in
       { impl with desc = Econstdecl(f, e) } :: acc
    | Efundecl(f, ({ f_args = p_list; f_body = e; f_env = f_env } as body)) ->
       let f_env, renaming = build f_env in
       let p_list = List.map (pattern renaming) p_list in
       let e = expression renaming e in
       let body = { body with f_args = p_list; f_body = e; f_env = f_env } in
       (* store the code into the global symbol table *)
       store f body;
       { impl with desc = Efundecl(f, body) } :: acc
    | _ -> impl :: acc
        
let implementation_list impl_list = Misc.fold implementation impl_list
