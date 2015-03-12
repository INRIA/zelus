(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* Mark functions to be inlined. *)
(* For a function definition: f(x) = y where ... k = g(e) ... *)
(* the call to g is inlined when [x: a], [y: b] and [g: b -> a] *)
(* that is, the call to [g] breaks an instantaneous dependence between [x] and [y] *)

open Zelus
open Causal

let causality_of_pattern_list p_list =
  List.fold_left
    (fun acc { p_caus = c_list } -> Causal.union acc c_list) [] p_list

let causality_of_exp acc { e_caus = c_list } = Causal.union acc c_list

let causality_of_exp_list e_list = List.fold_left causality_of_exp [] e_list
						  
(* remove dependence variables which appear in both *)
(*[c_in] and [c_out] *)
let rec only_once c_in c_out =
  let c_in =
    List.fold_left (fun acc c -> Causal.remove c acc) c_in c_out in
  let c_out =
    List.fold_left (fun acc c -> Causal.remove c acc) c_out c_in in
  c_in, c_out

(* Hypothesis: [c_in] and [c_out] are disjoint *)
(* A function call [res = f(arg)] is inlined if *)
(* [is_less_than_lists c_in c_arg] and [is_less_than_list c_arg c_out] *)
(* or [is_less_than_lists c_res c_arg] *)		  

(* for a function call [res = f(arg)], with [res: r1,...,rn] *)
(* [arg: a1,...,ak], a dependence [ai < rj] is added if conditions *)
(* (1) and (2) are verified *)
(* (1). not (rj < ai) - otherwise, this would add a cycle *)
(* (2). for any input in and output out. (in < ai) & (ai < out) => (in = out) *)
	   	   
let to_inline c_in c_out c_arg c_res =
  let c_arg, c_res = only_once c_arg c_res in
  
  let i = Causal.is_less_than_lists c_res c_arg in
  let i = if i then true
	  else (Causal.is_less_than_lists c_in c_arg) &&
		 (Causal.is_less_than_lists c_res c_out) in
  (* strictification of the function application in case *)
  (* inlining is useless *)
  if not i then
    List.iter
      (fun c_arg ->
       List.iter (fun c_res -> Causal.ctype_before_ctype c_arg c_res) c_res)
      c_arg;
  i

(* generic translation for match handlers *)
let match_handler body ({ m_body = b } as m_h) = { m_h with m_body = body b }

(* generic translation function for present handlers *)
let present_handler scondpat body ({ p_cond = sc; p_body = b } as p_h) =
  { p_h with p_cond = scondpat sc; p_body = body b }

(* Mark function calls [y = f(e)] to be inlined *)
let rec exp c_in c_out e =
  let rec exp ({ e_desc = desc; e_caus = c_list } as e) =
    let desc = match desc with
      | Elocal _ | Eglobal _ | Econst _
      | Econstr0 _ | Elast _ | Eperiod _ -> desc
      | Eapp(Eop(false, f), e_list) ->
	 let e_list = List.map exp e_list in
	 let c_arg = causality_of_exp_list e_list in
	 let c_res = causality_of_exp [] e in
	 let i = to_inline c_in c_out c_arg c_res in
	 Eapp(Eop(i, f), e_list)
      | Eapp(Eevery(false, f), e_list) ->
	 let e_list = List.map exp e_list in
	 let c_arg = causality_of_exp_list e_list in
	 let c_res = causality_of_exp [] e in
	 let i = to_inline c_in c_out c_arg c_res in
	 Eapp(Eevery(i, f), e_list)
      | Eapp(op, e_list) -> Eapp(op, List.map exp e_list)
      | Etuple(e_list) -> Etuple(List.map exp e_list)
      | Erecord_access(e, m) -> Erecord_access(exp e, m)
      | Erecord(m_e_list) ->
	 Erecord(List.map (fun (m, e) -> (m, exp e)) m_e_list)
      | Etypeconstraint(e, ty) -> Etypeconstraint(exp e, ty)
      | Epresent(p_h_list, e_opt) ->
	 Epresent(List.map (present_handler (scondpat c_in c_out) exp) p_h_list,
		  Misc.optional_map exp e_opt)
      | Ematch(total, e, m_h_list) ->
	 Ematch(total, exp e, List.map (match_handler exp) m_h_list)
      | Elet(l, e) ->
	 Elet(local c_in c_out l, exp e)
      | Eseq(e1, e2) -> Eseq(exp e1, exp e2) in
    { e with e_desc = desc } in
  exp e

and local c_in c_out ({ l_eq = eq_list } as l) =
  { l with l_eq = List.map (equation c_in c_out) eq_list }

and equation c_in c_out ({ eq_desc = desc } as eq) =
  let desc = match desc with
    | EQeq(p, e) -> EQeq(p, exp c_in c_out e)
    | EQder(n, e, e_opt, p_h_list) ->
       EQder(n, exp c_in c_out e, Misc.optional_map (exp c_in c_out) e_opt,
	     List.map
	       (present_handler (scondpat c_in c_out) (exp c_in c_out))
	       p_h_list)
    | EQinit(n, e) -> EQinit(n, exp c_in c_out e)
    | EQnext(n, e, e_opt) -> EQnext(n, exp c_in c_out e,
				    Misc.optional_map (exp c_in c_out) e_opt)
    | EQset(n, e) -> EQset(n, exp c_in c_out e)
    | EQautomaton(is_weak, s_h_list, se_opt) ->
       EQautomaton(is_weak, List.map (state_handler c_in c_out) s_h_list,
		   Misc.optional_map (state c_in c_out) se_opt)
    | EQpresent(p_h_list, b_opt) ->
       EQpresent(List.map
		   (present_handler (scondpat c_in c_out) (block c_in c_out))
		   p_h_list,
		 Misc.optional_map (block c_in c_out) b_opt)
    | EQmatch(total, e, m_h_list) ->
       EQmatch(total, exp c_in c_out e,
	       List.map (match_handler (block c_in c_out)) m_h_list)
    | EQreset(eq_list, e) ->
       EQreset(List.map (equation c_in c_out) eq_list, exp c_in c_out e)
    | EQemit(n, e_opt) ->
       EQemit(n, Misc.optional_map (exp c_in c_out) e_opt)
    | EQblock(b) -> EQblock(block c_in c_out b) in
  { eq with eq_desc = desc }

and scondpat c_in c_out ({ desc = desc } as sc) =
  let desc = match desc with
    | Econdand(sc1, sc2) ->
       Econdand(scondpat c_in c_out sc1, scondpat c_in c_out sc2)
  | Econdor(sc1, sc2) ->
     Econdor(scondpat c_in c_out sc1, scondpat c_in c_out sc2)
  | Econdexp(e) -> Econdexp(exp c_in c_out e)
  | Econdpat(e, p) -> Econdpat(exp c_in c_out e, p)
  | Econdon(sc, e) -> Econdon(scondpat c_in c_out sc, exp c_in c_out e) in
  { sc with desc = desc }     
				   
and state_handler c_in c_out ({ s_body = b; s_trans = trans } as sh) =
  { sh with s_body = block c_in c_out b;
	    s_trans = List.map (escape c_in c_out) trans }

and state c_in c_out ({ desc = desc } as se) =
  let desc = match desc with
    | Estate0 _ -> desc
    | Estate1(id, e_list) -> Estate1(id, List.map (exp c_in c_out) e_list) in
  { se with desc = desc }

and block c_in c_out ({ b_locals = l_list; b_body = eq_list } as b) =
  { b with b_locals = List.map (local c_in c_out) l_list;
	   b_body = List.map (equation c_in c_out) eq_list }

and escape c_in c_out
	   ({ e_cond = sc; e_block = b_opt; e_next_state = se } as esc) =
  { esc with e_cond = scondpat c_in c_out sc;
	     e_block = Misc.optional_map (block c_in c_out) b_opt;
	     e_next_state = state c_in c_out se }
    
let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
  | Efundecl(n, ({ f_args = p_list; f_body = e } as body)) ->
     let c_in = causality_of_pattern_list p_list in
     let c_out = causality_of_exp [] e in
     let e = exp c_in c_out e in
     { impl with desc = Efundecl(n, { body with f_body = e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
					      
