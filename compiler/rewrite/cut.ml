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
(* add extra copy variables for [last x] before static scheduling *)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

(* Make an equation [lx = last x] *)
let eq_last lx x ty = eqmake (EQeq(pmake (Evarpat(lx)) ty, emake (Elast(x)) ty))

(* Add an equation [lx = last x] if x in Dom(subst) *)
let add_eq_last subst x ty eq_list =
  try let lx = Env.find x subst in (eq_last lx x ty) :: eq_list
  with Not_found -> eq_list
		      
(* Computes the set of variables [last x] from [b_env] *)
let env subst b_env =
  let last x ({ t_typ = ty; t_sort = sort } as entry) (env, subst, eq_list) =
    match sort with
    | Smem { m_previous = true; m_init = Some i } -> 
       let lx = Ident.fresh "l" in
       Env.add lx { entry with t_sort = Deftypes.variable } env,
       Env.add x lx subst,
       (match i with None -> eq_list | Some _ -> (eq_last lx x ty) :: eq_list)
    | Sstatic | Sval | Svar _ | Smem _ -> env, subst, eq_list in
  Env.fold last b_env (b_env, subst, [])
    
(* replace occurrences of [last x] by [lx]. [subst(x) = lx] *)
let rec exp subst ({ e_desc } as e) = 
  let e_desc = match e_desc with
    | Elast(x) ->
       begin try Elocal(Env.find x subst) with Not_found -> e_desc end
    | Elocal _ | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> e_desc
    | Etuple(e_list) ->
       Etuple (List.map (exp subst) e_list)
    | Eop(op, e_list) -> Eop(op, List.map (exp subst) e_list)
    | Eapp(app, e_op, e_list) ->
       let e_list = List.map (exp subst) e_list in
       Eapp(app, exp subst e_op, e_list)
    | Erecord(label_e_list) ->
       let label_e_list =
	 List.map (fun (l, e) -> (l, exp subst e)) label_e_list in
       Erecord(label_e_list)
    | Erecord_access(e1, longname) ->
       Erecord_access(exp subst e1, longname)
    | Etypeconstraint(e1, ty) ->
       Etypeconstraint(exp subst e1, ty)
    | Elet(l, e) -> 
       let l, subst = local subst l in Elet(l, exp subst e)
    | Eseq(e1, e2) -> 
       Eseq(exp subst e1, exp subst e2)
    | Epresent _ | Ematch _ | Eblock _ -> assert false in
  { e with e_desc = e_desc }
    
(** Translation of equations. *)
and equation subst eq_list ({ eq_desc } as eq) =
  match eq_desc with
  | EQeq(p, e) -> 
     { eq with eq_desc = EQeq(p, exp subst e) } :: eq_list
  | EQpluseq(x, e) -> 
     { eq with eq_desc = EQpluseq(x, exp subst e) } :: eq_list
  | EQinit(x, e0) ->
     (* add an equation [lx = last x] *)
     let eq_list = add_eq_last subst x e0.e_typ eq_list in
     { eq with eq_desc = EQinit(x, exp subst e0) } :: eq_list
  | EQreset([{ eq_desc = EQinit(x, e0) } as eq_init], e) ->
     (* add an equation [lx = last x] *)
     let eq_list = add_eq_last subst x e0.e_typ eq_list in
     { eq with eq_desc =
		 EQreset([{ eq_init with eq_desc = EQinit(x, exp subst e0) }],
			 exp subst e) } :: eq_list
  | EQmatch(total, e, p_h_list) ->
     let p_h_list = 
       List.map
	 (fun ({ m_body = b } as h) -> { h with m_body = block subst b }) 
	 p_h_list in
     { eq with eq_desc = EQmatch(total, exp subst e, p_h_list) } :: eq_list
  | EQreset(res_eq_list, e) ->
     let res_eq_list = equation_list subst res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, exp subst e) } :: eq_list
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list subst and_eq_list) } :: eq_list
  | EQbefore(before_eq_list) ->
     { eq with eq_desc =
		 EQbefore(equation_list subst before_eq_list) } :: eq_list
  | EQder(x, e, None, []) ->
     { eq with eq_desc = EQder(x, exp subst e, None, []) } :: eq_list
  | EQblock(b) -> { eq with eq_desc = EQblock(block subst b) } :: eq_list
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(x, e) -> Einput(x, exp subst e)
	 | Eoutput _ -> desc
	 | Eindex(x, e1, e2) ->
	    Eindex(x, exp subst e1, exp subst e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, exp subst e)
	 | Einit_value(x, e, c_opt) ->
	    Einit_value(x, exp subst e, c_opt) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block subst b_eq_list in
       { eq with eq_desc =
		   EQforall { body with for_index = i_list;
					for_init = init_list;
					for_body = b_eq_list } }
     :: eq_list
  | EQpresent _ | EQautomaton _ | EQder _ | EQemit _ | EQnext _ -> assert false
									  
and equation_list subst eq_list =
  let eq_list = List.fold_left (equation subst) [] eq_list in
  List.rev eq_list
						 
and block subst ({ b_body = eq_list; b_env = b_env } as b) =
  (* Identify variables [last x] in [b_env] *)
  let b_env, subst, eq_last_list = env subst b_env in
  let eq_list = equation_list subst eq_list in
  { b with b_body = eq_last_list @ eq_list; b_env = b_env }
    
and local subst ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_env, subst, eq_last_list = env subst l_env in
  let l_eq_list = equation_list subst l_eq_list in
  { l with l_eq = eq_last_list @ l_eq_list; l_env = l_env }, subst
							       
let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _
  | Efundecl(_, { f_kind = S | A }) -> impl
  | Efundecl(n, ({ f_body = e; f_env = f_env } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp Env.empty e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
					      
