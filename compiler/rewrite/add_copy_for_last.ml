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

(* add an equation [lx = last x] for every variable declared in block *)
(* of equations and replace [last x] by lx *)
(* this step is necessary to make static scheduling possible. It may *)
(* introduce useless copies and is not idempotent. We may add a graph *)
(* argument later to prevent from introducing copies for equations of  *)
(* the form [lx = last x] *)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

(* Make an equation [lx = last x] *)
let eq_last lx x ty = eqmake (EQeq(pmake (Evarpat(lx)) ty, emake (Elast(x)) ty))

let add x ty (env, subst, eq_list) =
  let lx = Ident.fresh "l" in
  Env.add lx { t_typ = ty; t_sort = Deftypes.variable } env,
  Env.add x lx subst,
  (eq_last lx x ty) :: eq_list
                         
(* Computes the set of variables [last x] from [b_env] *)
let env subst b_env =
  let last x { t_typ = ty; t_sort = sort } (env, subst, eq_list) =
    match sort with
    | Smem { m_previous = true } -> add x ty (env, subst, eq_list)
    | Sstatic | Sval | Svar _ | Smem _ -> env, subst, eq_list in
  Env.fold last b_env (Env.empty, subst, [])
    
(* [extend_block b env eq_list] returns a block in which [env] and [eq_list] *)
(* are added to the environment and the set of equations *)
let extend_block
      ({ b_vars = b_vars; b_env = b_env; b_body = body_eq_list } as b)
      env eq_list =
  let b_vars =
    Env.fold (fun i entry acc -> Zaux.vardec_from_entry i entry :: acc)
             env b_vars in
  { b with b_vars = b_vars; b_env = Env.append env b_env;
           b_body = eq_list @ body_eq_list }
	 
(* translating a present statement *)
let present_handlers scondpat body p_h_list =
  List.map
    (fun ({ p_cond = scpat; p_body = b } as handler) ->
      { handler with p_cond = scondpat scpat; p_body = body b })
    p_h_list

(* replace some occurrences of [last x] by [lx]. [subst(x) = lx] *)
let rec exp subst ({ e_desc } as e) = 
  let e_desc = match e_desc with
    | Elast(x) ->
       begin try Elocal(Env.find x subst) with Not_found -> e_desc end
    | Elocal _ | Econst _ | Econstr0 _ | Eglobal _ -> e_desc
    | Etuple(e_list) ->
       Etuple (List.map (exp subst) e_list)
    | Econstr1(c, e_list) -> Econstr1(c, List.map (exp subst) e_list)
    | Eop(op, e_list) -> Eop(op, List.map (exp subst) e_list)
    | Eapp(app, e_op, e_list) ->
       let e_list = List.map (exp subst) e_list in
       Eapp(app, exp subst e_op, e_list)
    | Erecord(label_e_list) ->
       let label_e_list =
	 List.map (fun (l, e) -> (l, exp subst e)) label_e_list in
       Erecord(label_e_list)
    | Erecord_access(e_record, longname) ->
       Erecord_access(exp subst e_record, longname)
    | Erecord_with(e_record, label_e_list) ->
       let label_e_list =
	 List.map (fun (l, e) -> (l, exp subst e)) label_e_list in
       Erecord_with(exp subst e_record, label_e_list)
    | Etypeconstraint(e1, ty) ->
       Etypeconstraint(exp subst e1, ty)
    | Elet(l, e) -> 
       let l, subst = local subst l in Elet(l, exp subst e)
    | Eseq(e1, e2) -> 
       Eseq(exp subst e1, exp subst e2)
    | Epresent(p_h_list, e_opt) ->
        let e_opt = Misc.optional_map (exp subst) e_opt in
        let p_h_list = present_handler_exp_list subst p_h_list in
        Epresent(p_h_list, e_opt)
    | Ematch(total, e, m_h_list) ->
        let e = exp subst e in
        let m_h_list = match_handler_exp_list subst m_h_list in
        Ematch(total, e, m_h_list)
    | Eblock(b, e) ->
        let subst, b = block_eq_list_with_substitution subst b in
        Eblock(b, exp subst e)
    | Eperiod { p_phase = p1; p_period = p2 } ->
       Eperiod { p_phase = Misc.optional_map (exp subst) p1;
		 p_period = exp subst p2 } in
  { e with e_desc = e_desc }
    
(** Translation of equations. *)
and equation subst ({ eq_desc } as eq) =
  match eq_desc with
  | EQeq(p, e) -> 
     { eq with eq_desc = EQeq(p, exp subst e) }
  | EQpluseq(x, e) -> 
     { eq with eq_desc = EQpluseq(x, exp subst e) }
  | EQinit(x, e0) ->
     { eq with eq_desc = EQinit(x, exp subst e0) }
  | EQnext(n, e, e0_opt) -> 
     { eq with eq_desc = EQnext(n, exp subst e,
                                optional_map (exp subst) e0_opt) }
  | EQder(x, e, e0_opt, p_h_e_list) ->
     { eq with eq_desc = EQder(x, exp subst e, optional_map (exp subst) e0_opt,
                               present_handler_exp_list subst p_h_e_list) }
  | EQmatch(total, e, p_h_list) ->
     let p_h_list = 
       List.map
	 (fun ({ m_body = b } as h) ->
           { h with m_body = block_eq_list subst b }) 
	 p_h_list in
     { eq with eq_desc = EQmatch(total, exp subst e, p_h_list) }
  | EQreset(res_eq_list, e) ->
     let res_eq_list = equation_list subst res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, exp subst e) }
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list subst and_eq_list) }
  | EQbefore(before_eq_list) ->
     { eq with eq_desc =
		 EQbefore(equation_list subst before_eq_list) }
  | EQblock(b) -> { eq with eq_desc = EQblock(block_eq_list subst b) }
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(x, e) -> Einput(x, exp subst e)
	 | Eoutput _ -> desc
	 | Eindex(x, e1, e2) ->
	    Eindex(x, exp subst e1, exp subst e2) in
       { ind with desc = desc } in
     (* any use of [last x] where [x] is an accumulated value is renammed *)
     (* in [lx] with [lx] a local variable and [lx = last x] added *)
     let init acc ({ desc = desc } as ini) =
       let desc, acc = match desc with
	 | Einit_last(x, e) ->
            Einit_last(x, exp subst e), add x e.e_typ acc in
       { ini with desc = desc }, acc in
     let i_list = List.map index i_list in
     let init_list, (env, subst, eq_list) =
       Misc.map_fold init (Env.empty, subst, []) init_list in
     let b_eq_list =
       extend_block (block_eq_list subst b_eq_list) env eq_list in
     { eq with eq_desc =
		 EQforall { body with for_index = i_list;
				      for_init = init_list;
				      for_body = b_eq_list } }
  | EQpresent(p_h_b_eq_list, b_opt) ->
     let p_h_b_eq_list = present_handler_block_eq_list subst p_h_b_eq_list in
     let b_opt = 
       match b_opt with
       | None -> None | Some(b) -> Some(block_eq_list subst b) in
     { eq with eq_desc = EQpresent(p_h_b_eq_list, b_opt) }
  | EQautomaton(is_weak, state_handler_list, se_opt) ->
     (* translating a state *)
     let state subst ({ desc = desc; loc = loc } as se) =
       match desc with
       | Estate0 _ -> se
       | Estate1(n, e_list) ->
          { se with desc = Estate1(n, List.map (exp subst) e_list) } in
     let escape subst
                ({ e_cond = scpat; e_block = b_opt;
                   e_next_state = se } as esc) =
       let scpat = scondpat subst scpat in
       let b_opt = Misc.optional_map (block_eq_list subst) b_opt in
       let se = state subst se in
       { esc with e_cond = scpat; e_block = b_opt; e_next_state = se } in
     let handler subst ({ s_body = b; s_trans = trans } as h) =
       { h with s_body = block_eq_list subst b;
                s_trans = List.map (escape subst) trans } in
     { eq with eq_desc =
                 EQautomaton(is_weak,
                             List.map (handler subst) state_handler_list,
                             Misc.optional_map (state subst) se_opt) }
  | EQemit(name, e_opt) -> 
     { eq with eq_desc = EQemit(name, optional_map (exp subst) e_opt) }
  
									  
and equation_list subst eq_list = List.map (equation subst) eq_list
						 
(* Translate a generic block *)
and block_eq_list_with_substitution subst
				    ({ b_vars = vardec_list;
				       b_locals = l_list; b_body = eq_list;
				       b_env = b_env } as b) =
  (* Identify variables [last x] in [b_env] *)
  let b_env_last_list, subst, eq_last_list = env subst b_env in
  let l_list, subst = locals subst l_list in
  (* translate the body. *)
  let eq_list = equation_list subst eq_list in
  subst,
  extend_block { b with b_locals = l_list; b_body = eq_list }
    b_env_last_list eq_last_list

and block_eq_list subst b =
  let _, b = block_eq_list_with_substitution subst b in b
    
and present_handler_exp_list subst p_h_e_list =
  present_handlers (scondpat subst) (exp subst) p_h_e_list
                   
and present_handler_block_eq_list subst p_h_b_eq_list =
  present_handlers (scondpat subst) (block_eq_list subst) p_h_b_eq_list
                   
and match_handler_exp_list subst m_h_list =
  List.map (fun ({ m_body = e } as handler) -> 
      { handler with m_body = exp subst e }) m_h_list    
    
and match_handler_block_eq_list subst m_h_list =
  List.map (fun ({ m_body = b } as handler) -> 
      { handler with m_body = block_eq_list subst b }) m_h_list    

and local subst ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_env_last_list, subst, eq_last_list = env subst l_env in
  let l_eq_list = equation_list subst l_eq_list in
  { l with l_eq = eq_last_list @ l_eq_list;
	   l_env = Env.append l_env_last_list l_env }, subst

and locals subst l_list =
  match l_list with
  | [] -> [], subst
  | l :: l_list ->
     let l, subst = local subst l in
     let l_list, subst = locals subst l_list in
     l :: l_list, subst
                    
and scondpat subst ({ desc = desc } as scpat) =
  let desc = match desc with
    | Econdand(scpat1, scpat2) ->
       Econdand(scondpat subst scpat1, scondpat subst scpat2)
    | Econdor(scpat1, scpat2) ->
       Econdor(scondpat subst scpat1, scondpat subst scpat2)
    | Econdexp(e) -> Econdexp(exp subst e)
    | Econdpat(e, p) -> Econdpat(exp subst e, p)
    | Econdon(scpat, e) -> Econdon(scondpat subst scpat, exp subst e) in
  { scpat with desc = desc }

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _
  | Efundecl(_, { f_kind = S | A }) -> impl
  | Efundecl(n, ({ f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp Env.empty e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
