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
(* add extra copy variables for [last x] before static scheduling *)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

let eq_last lx x ty = eqmake (EQeq(pmake (Evarpat(lx)) ty, emake (Elast(x)) ty))

(* Computes the set of variables [last x] from [b_env] *)
let env subst b_env =
  let last x ({ t_typ = ty; t_sort = sort } as entry) (env, subst, eq_list) =
    match sort with
    | Smem { m_previous = true } -> 
       let lx = Ident.fresh "l" in
       Env.add lx { entry with t_sort = Deftypes.value } env,
       Env.add x lx subst,
       (eq_last lx x ty) :: eq_list
    | Sval | Svar _ | Smem _ -> env, subst, eq_list in
  Env.fold last b_env (b_env, subst, [])
    
(* replace occurrences of [last x] by [lx]. [subst(x) = lx] *)
let rec exp subst ({ e_desc } as e) = 
  let e_desc = match e_desc with
    | Elast(x) ->
      begin try Elocal(Env.find x subst) with Not_found -> e_desc end
    | Elocal _ | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> e_desc
    | Etuple(e_list) ->
      Etuple (List.map (exp subst) e_list)
    | Eapp(op, e_list) ->
      let e_list = List.map (exp subst) e_list in
      Eapp(op, e_list)
    | Erecord(label_e_list) ->
      let label_e_list = List.map (fun (l, e) -> (l, exp subst e)) label_e_list in
      Erecord(label_e_list)
    | Erecord_access(e1, longname) ->
      Erecord_access(exp subst e1, longname)
    | Etypeconstraint(e1, ty) ->
      Etypeconstraint(exp subst e1, ty)
    | Elet(l, e) -> 
      let l, subst = local subst l in Elet(l, exp subst e)
    | Eseq(e1, e2) -> 
      Eseq(exp subst e1, exp subst e2)
    | Epresent _ | Ematch _ -> assert false in
  { e with e_desc = e_desc }
	
(** Translation of equations. *)
and equation subst eq_list ({ eq_desc } as eq) =
  match eq_desc with
    | EQeq(p, e) -> 
      { eq with eq_desc = EQeq(p, exp subst e) } :: eq_list
    | EQpluseq(n, e) -> 
      { eq with eq_desc = EQpluseq(n, exp subst e) } :: eq_list
    | EQinit(n, e0) ->
      { eq with eq_desc = EQinit(n, exp subst e0) } :: eq_list
    | EQmatch(total, e, p_h_list) ->
      let p_h_list = 
	List.map (fun ({ m_body = b } as h) -> { h with m_body = block subst b }) 
	  p_h_list in
      { eq with eq_desc = EQmatch(total, exp subst e, p_h_list) } :: eq_list
    | EQreset(res_eq_list, e) ->
      let res_eq_list = equation_list subst res_eq_list in
      { eq with eq_desc = EQreset(res_eq_list, exp subst e) } :: eq_list
    | EQder(n, e, None, []) ->
      { eq with eq_desc = EQder(n, exp subst e, None, []) } :: eq_list
    | EQblock(b) -> { eq with eq_desc = EQblock(block subst b) } :: eq_list
    | EQpresent _ | EQautomaton _ | EQder _ | EQemit _ | EQnext _ -> assert false
							       
and equation_list subst eq_list = List.fold_left (equation subst) [] eq_list

and block subst ({ b_locals = l_list; b_body = eq_list; b_env = b_env } as b) =
  (* Identify variables [last x] in [b_env] *)
  let b_env, subst, eq_last_list = env subst b_env in
  let l_list, subst = 
    List.fold_left
      (fun (l_list, subst) l ->
       let l, subst = local subst l in l :: l_list, subst)
      ([], subst) l_list in
  let eq_list = equation_list subst eq_list in
  { b with b_locals = List.rev l_list;
    b_body = eq_last_list @ eq_list; b_env = b_env }
  
and local subst ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_env, subst, eq_last_list = env subst l_env in
  let l_eq_list = equation_list subst l_eq_list in
  { l with l_eq = eq_last_list @ l_eq_list; l_env = l_env }, subst

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl(_, { f_kind = A }) -> impl
  | Efundecl(n, ({ f_body = e; f_env = f_env } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp Env.empty e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list

