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

(* Translation of fby/pre/next/up into init/last *)
(* After this pass equations are of the form: *)
(* eq ::= x = e | x = e | der x = e | x = up(e) *)
(*              | init x = e *)
(*              | match e with P1 -> b1 | ... Pn -> bn *)
(*
    [e1 fby e2] => [let init x = e1 and x = e2 in last x]

    [pre(e)] => [let x = e in last x]

    [next x = e] => [x = e] and replace all occ. of [x] by [last x]

    [up(e)] => [let x = up(e) in x]
*)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

let let_make is_init is_up x ty eq_list e =
  let entry ty =
    let mem = Deftypes.previous Deftypes.empty_mem in
    let mem  = if is_init then Deftypes.initialized mem else mem in
    let sort = if is_up then Deftypes.zero mem else Deftypes.Smem mem in
    { t_sort = sort; t_typ = ty } in
  emake (Elet({ l_eq = eq_list; l_env = Env.singleton x (entry ty); 
		l_loc = no_location }, e)) e.e_typ

(* Computes the set of variables modified by a "next" from an environment *)
let env subst b_env =
  let change n ({ t_sort = sort } as entry) (env, subst) =
    match sort with
    | Smem ({ m_next = Some(true) } as m) -> 
      Env.add n { entry with t_sort = Smem { m with m_next = Some(false); 
						    m_previous = true } } env,
      S.add n subst
    | Sval | Svar _ | Smem _ -> Env.add n entry env, subst in
  Env.fold change b_env (Env.empty, subst)

(** Translation of expressions. Replaces [x] by [last x] for all variables *)
(* that appear in [subst] *)
let rec exp subst e = 
  match e.e_desc with
  | Elocal(x) -> if S.mem x subst then { e with e_desc = Elast(x) } else e
  | Econst _ | Econstr0 _ | Eglobal _ | Elast _ | Eperiod _ -> e
  | Etuple(e_list) ->
     { e with e_desc = Etuple (List.map (exp subst) e_list) }
  | Eapp(Efby, [e1; e2]) ->
     let e1 = exp subst e1 in
     let e2 = exp subst e2 in
     (* turns it into [let init x = e1 and x = e2 in last x] *)
     let x = Ident.fresh "m" in
     let_make true false x e1.e_typ [eq_init x e1; eq_make x e2] (last x e1.e_typ)
  | Eapp(Eunarypre, [e1]) ->
     let e1 = exp subst e1 in
     (* turns it into [let x = e1 in last x] *)
     let x = Ident.fresh "m" in
     let_make false false x e1.e_typ [eq_make x e1] (last x e1.e_typ)
  | Eapp(Eup, [e1]) ->
     let e1 = exp subst e1 in
     (* turns it into [let x = up(e1) in x] *)
     let x = Ident.fresh "m" in
     let_make false true x e1.e_typ [eq_make x (up e1)] (var x e1.e_typ)
  | Eapp(op, e_list) ->
     let e_list = List.map (exp subst) e_list in
     { e with e_desc = Eapp(op, e_list) }
  | Erecord(label_e_list) ->
     let label_e_list = List.map (fun (l, e) -> (l, exp subst e)) label_e_list in
     { e with e_desc = Erecord(label_e_list) }
  | Erecord_access(e1, longname) ->
     { e with e_desc = Erecord_access(exp subst e1, longname) }
  | Etypeconstraint(e1, ty) ->
     { e with e_desc = Etypeconstraint(exp subst e1, ty) }
  | Elet(l, e) -> 
     let l, subst = local subst l in { e with e_desc = Elet(l, exp subst e) }
  | Eseq(e1, e2) -> 
     { e with e_desc = Eseq(exp subst e1, exp subst e2) }
  | Epresent _ | Ematch _ -> assert false
	
(** Translation of equations. *)
and equation subst eq_list ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(p, e) -> 
     { eq with eq_desc = EQeq(p, exp subst e) } :: eq_list
  | EQnext(n, e, None) ->
     { eq with eq_desc = EQeq(varpat n e.e_typ, exp subst e) } :: eq_list
  | EQnext(n, e, Some(e0)) ->
     let e = exp subst e in
     let e0 = exp subst e0 in
     { eq with eq_desc = EQinit(n, e0) } :: 
       { eq with eq_desc = EQeq(varpat n e.e_typ, e) } :: eq_list
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
  | EQpresent _ | EQautomaton _ | EQder _ | EQemit _ -> assert false
							       
and equation_list subst eq_list = List.fold_left (equation subst) [] eq_list

and block subst ({ b_locals = l_list; b_body = eq_list; b_env = b_env } as b) =
  (* Identify which defined variable is a modified by a "next". *)
  (* Change its status to *)
  (* become a "last" variable *)
  let b_env, subst = env subst b_env in
  let l_list, subst = 
    List.fold_left
      (fun (l_list, subst) l -> let l, subst = local subst l in l :: l_list, subst)
      ([], subst) l_list in
  let eq_list = equation_list subst eq_list in
  { b with b_locals = List.rev l_list; b_body = eq_list; b_env = b_env }
  
and local subst ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_env, subst = env subst l_env in
  let l_eq_list = equation_list subst l_eq_list in
  { l with l_eq = l_eq_list; l_env = l_env }, subst

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl(_, { f_kind = A }) -> impl
  | Efundecl(n, ({ f_body = e; f_env = f_env } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp S.empty e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
