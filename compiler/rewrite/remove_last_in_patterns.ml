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

(* All variables in patterns must be values only                          *)
(* e.g., function parameters, patterns in pattern matching handlers, etc. *)
(* Any expression [last x] where [x] is expected to be a value            *)
(* is rewritten [lx] and equations [lx = last m and m = x] are introduced *)

(* Example:
 *- [let node f(x) = ... last x...] is rewritten
 *- [let node f(x) = let m = x and lx = last m in ... lx ...]
 *- [match e with P(...x...) -> 
       let d1 in ... last x ... let dn in do ... last x ... done]
 *- [match e with P(...x...) -> 
       let lx = last m and m = x in
       let d1 in ... lx ... let dn in do ... lx ... done]
 *- [present
       e(...x...) ->
         let d1 in ... last x ... let dn in do ... last x ... done]
 *- [present
       e(...x...) ->
         let lx = last m and m = x in 
         ... lx ... let dn in do ... lx ... done]
 *)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

(* Make equations [lx = last m and m = x] *)
let eq_lx_last_m_m_x lx m x ty eq_list =
  (eqmake (EQeq(pmake (Evarpat(lx)) ty, emake (Elast(m)) ty))) ::
  (eqmake (EQeq(pmake (Evarpat(m)) ty, emake (Elocal(x)) ty))) ::
    eq_list

let add x ty sort (env, new_env, subst, eq_list) =
  let lx = Ident.fresh "l" in
  let m = Ident.fresh "m" in
  Env.add x { t_typ = ty; t_sort = Deftypes.value } env,
  Env.add lx { t_typ = ty; t_sort = Deftypes.value }
    (Env.add m { t_typ = ty; t_sort = sort } new_env),
  Env.add x lx subst,
  eq_lx_last_m_m_x lx m x ty eq_list
                         
(* Computes the set of variables [last x] from [b_env] *)
(* turns all values in [b_env] to values *)
let valenv subst b_env =
  let last x ({ t_typ = ty; t_sort = sort } as entry)
        (env, new_env, subst, eq_list) =
    match sort with
    | Smem { m_previous = true } ->
       add x ty sort (env, new_env, subst, eq_list)
    | Smem { m_previous = false } ->
       Env.add x { entry with t_sort = Sval } env, new_env, subst, eq_list
    | Sstatic | Sval | Svar _ ->
       Env.add x entry env, new_env, subst, eq_list in
  Env.fold last b_env (Env.empty, Env.empty, subst, [])
    
(* [extend_block b env eq_list] returns a block *)
(* with an extra set of local declarations [eq_list] in front of it *)
let extend_block ({ b_locals = l_list } as b) env eq_list =
  { b with b_locals = (Zaux.make_local env eq_list) :: l_list }

(* translating a present statement *)
let present_handlers subst scondpat body p_h_list =
  List.map
    (fun ({ p_cond = scpat; p_body = b; p_env = p_env } as handler) ->
      let p_env, new_env, subst, eq_list = valenv subst p_env in
      let b = body subst b new_env eq_list in
     { handler with p_cond = scondpat subst scpat; p_env = p_env; p_body = b})
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
       let l = local subst l in Elet(l, exp subst e)
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
    | Eblock(b_eq_list, e) ->
        Eblock(block_eq_list subst b_eq_list, exp subst e)
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
     let p_h_list = match_handler_block_eq_list subst p_h_list in
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
		for_body = b_eq_list; for_in_env = for_in_env;
                for_out_env = for_out_env } as body) ->
     let for_in_env, new_in_env, subst, eq_in_list = valenv subst for_in_env in
     let for_out_env, new_out_env, subst, eq_out_list = valenv subst for_in_env in
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(x, e) -> Einput(x, exp subst e)
	 | Eoutput _ -> desc
	 | Eindex(x, e1, e2) ->
	    Eindex(x, exp subst e1, exp subst e2) in
       { ind with desc = desc } in
     (* any use of [last x] where [x] is an accumulated value is renammed *)
     (* in [lx] with [lx] a local variable and [lx = last x] added *)
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, exp subst e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block_eq_list subst b_eq_list in
     let b_eq_list = extend_block b_eq_list new_in_env eq_in_list in
     let b_eq_list = extend_block b_eq_list new_out_env eq_out_list in
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
                   e_next_state = se; e_env = e_env } as esc) =
       let e_env, new_env, subst, eq_list = valenv subst e_env in
       let scpat = scondpat subst scpat in
       let b_opt =
         match b_opt with
         | None -> if Env.is_empty new_env then None
                   else Some (Zaux.make_block new_env eq_list)
         | Some(b_eq_list) ->
            let b_eq_list = block_eq_list subst b_eq_list in
            let b_eq_list = extend_block b_eq_list new_env eq_list in
            Some(b_eq_list) in
       let se = state subst se in
       { esc with e_cond = scpat; e_block = b_opt; e_next_state = se;
                  e_env = e_env } in
     let handler subst ({ s_body = b; s_trans = trans; s_env = s_env } as h) =
       let s_env, new_env, subst, eq_list = valenv subst s_env in
       let b = block_eq_list subst b in
       let b = extend_block b new_env eq_list in
       { h with s_body = b;
                s_trans = List.map (escape subst) trans } in
     { eq with eq_desc =
                 EQautomaton(is_weak,
                             List.map (handler subst) state_handler_list,
                             Misc.optional_map (state subst) se_opt) }
  | EQemit(name, e_opt) -> 
     { eq with eq_desc = EQemit(name, optional_map (exp subst) e_opt) }
  
									  
and equation_list subst eq_list = List.map (equation subst) eq_list
						 
(* Translate a generic block *)
and block_eq_list subst ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list = locals subst l_list in
  (* translate the body. *)
  let eq_list = equation_list subst eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and present_handler_exp_list subst p_h_e_list =
  let exp subst e new_env eq_list =
    let e = exp subst e in
    Zaux.make_let new_env eq_list e in
  present_handlers subst scondpat exp p_h_e_list
                   
and present_handler_block_eq_list subst p_h_b_eq_list =
  let block_eq_list subst b new_env eq_list =
    let b = block_eq_list subst b in
    extend_block b new_env eq_list in
  present_handlers subst scondpat block_eq_list p_h_b_eq_list
                   
and match_handler_exp_list subst m_h_list =
  List.map (fun ({ m_body = e; m_env = m_env } as handler) -> 
      let m_env, new_env, subst, eq_list = valenv subst m_env in
      let e = exp subst e in
      let e = Zaux.make_let new_env eq_list e in
      { handler with m_body = e; m_env = m_env }) m_h_list    
    
and match_handler_block_eq_list subst m_h_list =
  List.map (fun ({ m_body = b; m_env = m_env } as handler) -> 
      let m_env, new_env, subst, eq_list = valenv subst m_env in
      let b = block_eq_list subst b in
      let b = extend_block b new_env eq_list in
      { handler with m_body = b; m_env = m_env }) m_h_list    

and local subst ({ l_eq = l_eq_list } as l) =
  let l_eq_list = equation_list subst l_eq_list in
  { l with l_eq = l_eq_list }

and locals subst l_list = List.map (local subst) l_list
                    
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
  | Efundecl(n, ({ f_body = e; f_env = f_env } as body)) ->
     let f_env, new_env, subst, eq_list = valenv Env.empty f_env in
     let e = exp subst e in
     let e = Zaux.make_let new_env eq_list e in
     { impl with desc = Efundecl(n, { body with f_env = f_env; f_body = e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
