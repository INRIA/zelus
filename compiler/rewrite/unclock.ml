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

(* Translation into Lustre *)
open Location
open Ident
open Zelus
open Deftypes

let eqmake desc = 
  { eq_desc = desc; eq_loc = no_location }
let make desc ty = 
  { e_desc = desc; e_loc = no_location; e_typ = ty }
let pmake desc ty = 
  { p_desc = desc; p_loc = no_location; p_typ = ty }
let varpat x ty = pmake (Evarpat(x)) ty
let var x ty = make (Elocal(x)) ty
let and_op e1 e2 = 
  make (Eapp(Eop(Modname { qual = "Pervasives"; id = "(&&)" }), [e1; e2]))
       Initial.typ_bool

type ck = | Ck_base | Ck_on of ck * exp
 
let on ck e = Ck_on(ck, e)

(* from a clock to a boolean expression *)
let rec clock = function
  | Ck_base -> make (Econst(Ebool(true))) Initial.typ_bool
  | Ck_on(Ck_base, e) -> e
  | Ck_on(ck, e) -> and_op (clock ck) e

(* environment *)

(* build an environment *)
let build_env env l_env = l_env

(* compute the set of shared variables *)
let shared_variables p_h_list =
  List.fold_left 
    (fun acc { m_body = { b_write = { dv = w } } } -> S.union acc w)
    S.empty p_h_list

(* Compute the initial values for registers *)
let rec init subst ({ eq_desc = desc } as eq) =
  match desc with
  | EQinit({ p_desc = Evarpat(x) }, e, _) -> Env.add x e subst
  | EQafter(eq_list, _) -> init_list subst eq_list
  | _ -> subst

and init_list subst eq_list = List.fold_left init subst eq_list
  
(* add equations of the form [x = v -> pre (if ck then e else x)] *)
(* for all variables appearing in [l_names] *)
(* [s_init = [e1/x1,...,en/xn] *)
let next s_init ck eq_list x e =
  let ifthenelse ck e1 e2 =
    { e1 with e_desc = Eapp(Eifthenelse, [e1; e2]) } in
  let minusgreater e1 e2 =
    { e1 with e_desc = Eapp(Eminusgreater, [e1; e2]) } in
  let pre_e = { e with e_desc = Eapp(Eunarypre,
				     [ifthenelse (clock ck) e (var x e.e_typ)]) } in
  let e = 
    try let i = Env.find x s_init in minusgreater i pre_e
    with Not_found -> pre_e in
  eqmake (EQeq(varpat x e.e_typ, e)) :: eq_list

(* [equation subst eq_list eq = eq_list] *)
let rec equation env s_init ck shared_names (eq_list, subst) 
		 ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq({ p_desc = Evarpat(x) }, e) when S.mem x shared_names -> 
     eq_list, Env.add x e subst
  | EQeq(p, e) -> eq :: eq_list, subst
  | EQnext({ p_desc = Evarpat(x) } as pat, e, None) -> 
     next s_init ck eq_list x e, subst
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
  | EQafter(after_eq_list, _) -> equation_list env (eq_list, subst) after_eq_list
  | EQemit _ | EQautomaton _ | EQpresent _ | EQder _ | EQreset _ -> assert false

and equation_list env (eq_list, subst) = 
  List.fold_left (equation env) (eq_list, subst) acc eq_list
 
and block env (eq_list, pat_subst_list) ck
	  ({ b_body = body_eq_list; b_env = n_env } as b) =
  let subst, n_env, n_list, next_eq_list = build_env subst n_env in
  (* compute the initial values for state variables *)
  let s_init = init Env.empty body_eq_list in
  (* translate the body *)
  let eq_list, subst = equation_list env (eq_list, Env.empty) body_eq_list in
  (* add equations of the form [x = v -> pre (if ck then e else x)] *)
  (* for every input [x\e] when [x] is a local variable and a register *)
  let eq_list, subst = next s_init ck eq_list subst in
  eq_list, subst

and local subst ({ l_eq = eq_list; l_env = l_env } as l) =
  let subst, l_env, _, next_eq_list = build_env subst l_env in
  let eq_list = equation_list subst next_eq_list eq_list in
  { l with l_eq = eq_list; l_env = l_env }

let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ 
      | Econstdecl _ | Efundecl(_, { f_kind = (A | D | AD) }) -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp Env.empty e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
