(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* causality check *)
(* sigma ::= forall a1,...,an:C.t1 -> t2 *)
(* t ::= t * ... * t | a *)

open Misc
open Ident
open Zelus
open Location
open Causal

(* lift a kind to a discrete one *)
let discrete = function | A -> A | C -> D | D -> D | AD -> AD

(** Causality analysis of a match handler *)
let match_handlers k env body m_h_list =
  let handler { m_pat = p; m_body = b } = 
    body k env b in
  corlist (List.map handler m_h_list)

(** Causality analysis of a present handler *)
let present_handlers k env scondpat body p_h_list =
  let handler { p_cond = scpat; p_body = b } =
    let t = scondpat k env scpat in
    cseq t (body (discrete k) env b) in
  corlist (List.map handler p_h_list)

(** Causality analysis of a block. *)
let block k env locals body
    { b_vars = n_list; b_locals = l_list; b_body = bo; b_loc = loc } =
  (* local names defined in [n_list] *)
  let l_env = List.fold_left (fun acc n -> S.add n acc) S.empty n_list in
  let env = S.union l_env env in        
  let c_locals = locals k env l_list in
  let c_body = body k env bo in
  let c = cseq c_locals c_body in
  Causal.check loc c;
  clear l_env c

(* cutting dependences with a delay operator *)
let rec pre = function
  | Cor(c1, c2) -> Cor(pre c1, pre c2)
  | Cand(c1, c2) -> Cand(pre c1, pre c2)
  | Cseq(c1, c2) -> Cseq(pre c1, pre c2)
  | Cread(x) -> Clastread(x)
  | (Cwrite _ | Clastread _ | Cempty) as c -> c

(* The causality of [last x]. Breaks a cycle in a discrete context. Not in *)
(* a continuous one *)
let lastread k x = match k with | C -> read x | A | AD | D -> lastread x

(** Computes the causality constraint for an expression under kind [k]. Dependences *)
(* are kept for names appearing in [env] only. *)
let rec exp k env { e_desc = desc; e_loc = loc } =
  match desc with
    | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> cempty
    | Elocal(x) -> if S.mem x env then read x else cempty
    | Elast(x) -> if S.mem x env then lastread k x else cempty
    | Etuple(e_list) -> candlist (List.map (exp k env) e_list)
    | Eapp(op, e_list) -> apply k env op e_list
    | Erecord_access(e, _) -> exp k env e
    | Erecord(l) -> candlist (List.map (fun (_, e) -> exp k env e) l)
    | Etypeconstraint(e, _) -> exp k env e
    | Elet(l, e_let) -> 
        let env, t_l = local k (env, cempty) l in
        let t = cseq t_l (exp k env e_let) in
        Causal.check loc t;
        t
    | Eseq(e1, e2) -> cseq (exp k env e1) (exp k env e2)
    | Epresent(p_h_e_list, e_opt) ->
        let t_p_h_e_list = present_handler_exp_list k env p_h_e_list in
	let t = opt (exp k env) e_opt in
	cor t_p_h_e_list t
    | Ematch(_, e, m_h_e_list) ->
        let t = exp k env e in
	let t_m_h_e_list = match_handler_exp_list k env m_h_e_list in
	cseq t t_m_h_e_list
      
(** Typing an application *)
and apply k env op e_list =
  match op, e_list with
    | Eunarypre, [e] -> pre (exp k env e)
    | Efby, [e1;e2] ->
        let t1 = exp k env e1 in
        let t2 = pre (exp k env e2) in
        candlist [t1; t2]
    | Eminusgreater, [e1;e2] ->
        let t1 = exp k env e1 in
        let t2 = exp k env e2 in
        candlist [t1; t2]
    | Eifthenelse, [e1; e2; e3] ->
        let t1 = exp k env e1 in
        let i2 = exp k env e2 in
        let i3 = exp k env e3 in
        cseq t1 (cor i2 i3)
    | (Eup | Etest | Edisc), [e1] -> exp k env e1
    | (Eon | Eop _ | Einitial), e_list -> candlist (List.map (exp k env) e_list)
    | _ -> assert false

and pattern { p_desc = desc } =
  match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> cempty
    | Evarpat(x) -> cwrite(x)
    | Etuplepat(pat_list) ->
        candlist (List.map pattern pat_list)
    | Erecordpat(l) -> candlist (List.map (fun (_, p) -> pattern p) l)
    | Etypeconstraintpat(p, _) -> pattern p
    | Eorpat(p1, _) -> pattern p1
    | Ealiaspat(p, n) -> cand (pattern p) (cwrite n)

(** Checking equations *)
and equation_list k env eq_list = candlist (List.map (equation k env) eq_list)

and equation k env eq =
  match eq.eq_desc with
    | EQeq(p, e) -> cseq (exp k env e) (pattern p)
    | EQder(n, e, e0_opt, p_h_e_list) ->
        let t_e0 = opt (exp k env) e0_opt in
        let t_list =
	  List.fold_left
	    (fun t { p_cond = scpat; p_body = e } ->
	      cor t (cseq (scondpat k env scpat) (exp k env e))) cempty p_h_e_list in
	cand (candlist [pre (exp k env e); t_e0]) t_list
    | EQinit(p, e0, e_opt) ->
        cseq (cand (exp k env e0) (opt (exp k env) e_opt)) (pattern p)
    | EQnext(p, e, e0_opt) ->
        cseq (pre (exp k env e)) (opt (exp k env) e0_opt)
    | EQautomaton(s_h_list, se_opt) ->
        let state k env { desc = desc } =
	    match desc with
	      | Estate0 _ -> cempty
	      | Estate1(_, e_list) -> candlist (List.map (exp k env) e_list) in
	(* handler *)
        let handler k env { s_body = b; s_until = until; s_unless = unless } =
          let escape k env t { e_cond = sc; e_block = b_opt; e_next_state = se } =
            cor t
	      (cseq (scondpat k env sc) 
		 (cseq 
		    (match b_opt with 
		      | None -> cempty | Some(b) -> block_eq_list (discrete k) env b)
		    (state (discrete k) env se))) in
          cseq (List.fold_left (escape k env) cempty unless)
            (cseq (block_eq_list k env b) 
	       (List.fold_left (escape k env) cempty until)) in
        cseq (opt (state k env) se_opt) 
	  (List.fold_left 
	     (fun t s_h -> cor t (handler k env s_h)) cempty s_h_list)
    | EQmatch(_, e, m_h_list) ->
        let t = match_handler_block_eq_list k env m_h_list in
        cseq (exp k env e) t
    | EQpresent(p_h_list, b_opt) ->
        let t_opt = 
	  match b_opt with | None -> cempty | Some(b) -> block_eq_list k env b in
        let t = present_handler_block_eq_list k env p_h_list in
	cor t_opt t
    | EQreset(b, e) -> cseq (exp k env e) (block_eq_list k env b)
    | EQemit(n, e_opt) ->
        let t = opt (exp k env) e_opt in
        cseq t (cwrite n)

and scondpat k env { desc = desc } =
  match desc with
    | Econdand(scpat1, scpat2) | Econdor(scpat1, scpat2) ->
        cand (scondpat k env scpat1) (scondpat k env scpat2)
    | Econdon(scpat1, e) -> cand (scondpat k env scpat1) (exp k env e)
    | Econdexp(e) | Econdpat(e, _) -> exp k env e

and present_handler_exp_list k env p_h_list =
  present_handlers k env scondpat exp p_h_list

and present_handler_block_eq_list k env p_h_list =
  present_handlers k env scondpat block_eq_list p_h_list

and match_handler_block_eq_list k env m_h_list =
  match_handlers k env block_eq_list m_h_list

and match_handler_exp_list k env m_h_list =
  match_handlers k env exp m_h_list

and block_eq_list k env b =
  let locals k env l_list =
    let _, t = List.fold_left (local k) (env, cempty) l_list in t in
  block k env locals equation_list b
  
and local k (env, t) { l_eq = eq_list; l_loc = loc; l_env = l_env } =
  let l_env = Env.fold (fun n _ acc -> S.add n acc) l_env S.empty in
  let env = S.union l_env env in
  let t_eq_list = equation_list k env eq_list in
  Causal.check loc t_eq_list;
  let t_eq_list = clear l_env t_eq_list in
  env, cseq t t_eq_list

let implementation ff impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(f, e) -> ignore (exp Zelus.A S.empty e) 
    | Efundecl(f, { f_kind = k; f_args = p_args; f_body = e }) ->
        let c = exp k S.empty e in
        (* output the signature *)
	if !Misc.print_causality then print_declaration ff f (p_args, c)

let implementation_list ff impl_list = List.iter (implementation ff) impl_list
