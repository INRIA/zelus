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

(* Applied to normalized expressions and equations *)
(* compiling the initialization [->], [initial clock] and [init x = ...] *)
(* Introduce an initialization bit [init i = true and i = false] *)
(* per control block when the block contains [init x = e] and *)
(* [e] is not static *)

open Misc
open Location
open Deftypes
open Zelus
open Zaux
open Ident

(** Static expressions *)
let rec static { e_desc = desc } =
  match desc with
  | Econst _ | Econstr0 _ -> true
  | Etuple(e_list) -> List.for_all static e_list
  | Erecord(qual_e_list) -> List.for_all (fun (_, e) -> static e) qual_e_list
  | Erecord_access(e, _) -> static e
  | _ -> false

let intro = function None -> Ident.fresh "i" | Some(i) -> i

(* Surround an equation by a reset *)
let reset i_opt eq =
  let equation i =
    { eq with eq_desc = EQreset([eq], last i Initial.typ_bool) } in
  let i = intro i_opt in
  equation i, Some(i)

(* Build a boolean condition from the initialization bit. *)
let condition i_opt = let i = intro i_opt in last i Initial.typ_bool, Some(i)

(* Introduce an equation [init i = true and i = false] *)
let intro_equation (i_names, i_opt) eq_list =
  match i_opt with
  | None -> eq_list, i_names
  | Some(i) -> Zaux.init i eq_list, i :: i_names
			 
(* Introduce the declaration for every name in [i_names] *)
let intro (i_names, i_opt) n_list env eq_list =
  let add (acc_n_list, acc_env_list) i =
    (Zaux.vardec i) :: acc_n_list,
    Env.add i (Deftypes.entry Deftypes.memory Initial.typ_bool) acc_env_list in
  let eq_list, i_names = intro_equation (i_names, i_opt) eq_list in
  let n_list, env = List.fold_left add (n_list, env) i_names in
  n_list, env, eq_list

(** Translation of equations. *)
(* If the equation contains an initialization with an non static *)
(* value, introduce a fresh initialization variable [i] *)
let rec equation (i_names, i_opt) ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(p, ({ e_desc = Eop(Eminusgreater, [e1; e2]) } as e)) ->
     (* [e1 -> e2 = if last i then e1 else e2] *)
     let cond, i_opt = condition i_opt in
     { eq with eq_desc =
		 EQeq(p,
		      { e with e_desc = Eop(Eifthenelse, [cond; e1; e2]) }) },
     (i_names, i_opt)
  | EQeq({ p_desc = Evarpat(x) } as p, { e_desc = Eop(Einitial, []) })
    -> (* [initial = true fby false] *)
     let cond, i_opt = condition i_opt in
     { eq with eq_desc = EQeq(p, cond) }, (i_names, i_opt)
  | EQeq _ | EQpluseq _ | EQder _ -> eq, (i_names, i_opt)
  | EQinit(x, e) ->
     if static e then eq, (i_names, i_opt)
     else let eq, i_opt = reset i_opt eq in eq, (i_names, i_opt)
  | EQmatch(total, e, m_h_list) ->
     let m_h_list =
       List.map (fun ({ m_body = b } as m_h) -> { m_h with m_body = block b })
		m_h_list in
     { eq with eq_desc = EQmatch(total, e, m_h_list) }, (i_names, i_opt)
  | EQreset(res_eq_list, e) ->
     let res_eq_list, i_names_i_opt =
       equation_list (i_names, None) res_eq_list in
     let res_eq_list, i_names = intro_equation i_names_i_opt res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, e) }, (i_names, i_opt)
  | EQand(and_eq_list) ->
     let and_eq_list, i_names_i_opt =
       equation_list (i_names, i_opt) and_eq_list in
     { eq with eq_desc = EQand(and_eq_list) }, i_names_i_opt
  | EQbefore(before_eq_list) ->
     let before_eq_list, i_names_i_opt =
       equation_list (i_names, i_opt) before_eq_list in
     { eq with eq_desc = EQbefore(before_eq_list) }, i_names_i_opt
  | EQforall ({ for_body = b_eq_list } as body) ->
     let b_eq_list = block b_eq_list in
     { eq with eq_desc = EQforall { body with for_body = b_eq_list } },
     (i_names, i_opt)
  | EQblock _ | EQemit _ | EQnext _ | EQautomaton _ | EQpresent _ ->
						       assert false

and equation_list i_names_i_opt eq_list =
  Misc.map_fold equation i_names_i_opt eq_list

and local ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, i_names_i_opt = equation_list ([], None) eq_list in
  let _, l_env, eq_list = intro i_names_i_opt [] l_env eq_list in
  { l with l_eq = eq_list; l_env = l_env }

(** Translation of blocks *)
and block ({ b_vars = n_list; b_body = eq_list; b_env = n_env } as b) =
  let eq_list, i_names_i_opt = equation_list ([], None) eq_list in
  let n_list, n_env, eq_list = intro i_names_i_opt n_list n_env eq_list in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }

(** Expressions. *)
let exp ({ e_desc = desc } as e) =
  let desc =
    match desc with
    | Elet(l, e) -> Elet(local l, e)
    | _ -> desc in
  { e with e_desc = desc }
 
let implementation impl =
  match impl.desc with
  | Efundecl(n, ({ f_kind = D | C; f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp e }) }
  | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list
