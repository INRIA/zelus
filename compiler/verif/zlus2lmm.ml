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

let eqmake loc pat e loc = 
  { Lmm.eq_lhs = pat; Lmm.eq_rhs = e; Lmm.eq_loc = loc }

type ck = | Ck_base | Ck_on of ck * Lmm.exp
 
let on ck e = Ck_on(ck, e)

(* from a clock to a boolean expression *)
let rec clock = function
  | Ck_base -> make (Econst(Ebool(true))) Initial.typ_bool
  | Ck_on(Ck_base, e) -> e
  | Ck_on(ck, e) -> and_op (clock ck) e

(* [equation subst eq_list eq = eq_list] *)
let rec equation ck acc { eq_desc = desc } =
  match desc with
  | EQeq({ p_desc = Evarpat(x) }, e) when S.mem x shared_names -> 
     eq_list, Env.add x e subst
  | EQeq(p, e) -> eq :: eq_list, subst
  | EQinit _ -> eq_list, subst
  | EQmatch(total, e, p_h_list) ->
     (* first compute the set of shared variables *)
     let s = shared_variables p_h_list in
     let handler (eq_list, pat_subst_list) { m_pat = p; m_body = b; m_env } =
       let ck = on ck p e in
       block env (eq_list, (p, Env.empty)) ck b in
     let eq_list, subst_list = List.fold_left handler (eq_list, []) p_h_list in
     let pat_subst_list = List.rev pat_subst_list in
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
