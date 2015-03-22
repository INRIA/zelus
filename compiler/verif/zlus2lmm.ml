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

(* Translation into Lustre-- *)

open Location
open Ident
open Zelus
open Deftypes

let eq_make pat e loc = 
  { Lmm.eq_lhs = pat; Lmm.eq_rhs = e; Lmm.eq_loc = no_location }

let make desc ty = { Lmm.e_desc = desc; Lmm.e_typ = ty; Lmm.e_loc = no_location }

let and_op e1 e2 =
  make (Eapp(Eop(Lident.Modname(Initial.pervasives_name "&&")),
	     [e1; e2])) Initial.typ_bool
       
type ck = | Ck_base | Ck_on of ck * Lmm.exp
 
let on ck e = Ck_on(ck, e)

(* from a clock to a boolean expression *)
let rec clock = function
  | Ck_base -> make (Econst(Ebool(true))) Initial.typ_bool
  | Ck_on(Ck_base, e) -> e
  | Ck_on(ck, e) -> and_op (clock ck) e

(* [equation ck eq = eq_list] *)
let rec equation ck { eq_desc = desc; eq_write = defnames } = 
  match desc with
    | EQeq(p, e) ->
      State.singleton (eq_make (pattern p) (expression ck e))
    | EQmatch(total, e, p_h_list) ->
      (* first translate [e] *)
      let e = expression ck e in
      (* then compute the set of shared variables *)
      let s = shared_variables defnames in
      let handler { m_pat = p; m_body = b } =
	let p = pattern p in
	let eq_p_e = pat_with_expression p e in
	let ck = on ck p e in
	let eq = block ck b in
	eq
      (* do it for all *)
      let p_h_list = List.map handler p_h_list in
      merge e pat_subst_list
  | EQemit _ | EQautomaton _ | EQpresent _ | EQder _ | EQreset _ -> assert false

and equation_list ck acc eq_list =  List.fold_left (equation ck) acc eq_list
 
and block ck acc ({ b_body = body_eq_list; b_env = n_env } as b) = acc
								     
let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ 
      | Econstdecl _ | Efundecl(_, { f_kind = (A | D | AD) }) -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp Env.empty e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
