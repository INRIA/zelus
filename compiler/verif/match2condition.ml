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

(* Rewriting of pattern matching into boolean conditions. *)
(* Warning: this is not what should be done to compile *)
(* pattern matching into sequential code; the result is inefficient. *)
(* For that, read Xavier Leroy's notes *)
(* at https://xavierleroy.org/dea/compil/matching.txt *)
(* or the ICFP'01 paper by Le Fessant and Maranget *)

(* Entry is:
match e1,...,en with
  p11,...,p1n -> a1
| ...
| pM1,...,pMn -> aM

Output is: let eqs in if c1 then ... else ...
*)

open Misc
open Zelus
open Zaux
open Ident
open Deftypes
    
type return = { eqs: eq State.t; env: tentry Env.t State.t }

let empty = { eqs = State.empty; env = State.empty }

let with_env env ({ env = env0 } as return) =
  { return with env = State.cons env env0 }

let with_eq eq ({ eqs = eqs } as return) =
  { return with eqs = State.cons eq eqs }

let and_op e1 e2 =
  if e1 = etrue then e2 else if e2 = etrue then e1
  else Zaux.and_op e1 e2
let or_op e1 e2 =
  if e1 = efalse then e2 else if e2 = efalse then e1
  else Zaux.or_op e1 e2

(* for a pair [pat, e] computes the equation [pat_v = e] and boolean *)
(* condition c where [pat_v] is only made of variables and [c] *)
(* is true when [pat] matches [e] *)
let rec filter return ({ p_desc = p_desc; p_typ = ty } as p) ({ e_desc } as e) =
  match p_desc, e_desc with
  | Ewildpat, _ -> Zaux.etrue, return
  | Evarpat(id), _ ->
      Zaux.etrue, with_eq (Zaux.eqmake (EQeq(p, e))) return
  | Econstpat(c), _ -> or_op (Zaux.const c ty) e, return
  | Econstr0pat(c), _ -> or_op (Zaux.constr0 c ty) e, return
  | Econstr1pat _, _ -> assert false
  | Etuplepat(p_list), Etuple(e_list) -> filter_list return p_list e_list
  | Etuplepat(p_list), _ ->
      (* filter (p1,...,pn)  e *)
      (* has the meaning of filter p1 (get e 0) ... filter pn (get e n) *)
      (* introduce n fresh names *)
     let n_ty_list =
       List.map (fun { p_typ = ty } -> Ident.fresh "", ty) p_list in
     let env =
       List.fold_left
         (fun acc (n, ty) -> Env.add n (Deftypes.entry Deftypes.value ty) acc)
         Env.empty n_ty_list in
     let e_list = List.map (fun (n, ty) -> Zaux.var n ty) n_ty_list in
     let v_list = List.map (fun (n, ty) -> Zaux.varpat n ty) n_ty_list in
     let cond, return = filter_list return p_list e_list in
     cond,
     with_env env
       (with_eq (Zaux.eqmake (EQeq(Zaux.tuplepat v_list, e))) return)
  | Ealiaspat(p, id), _ ->
     let cond, return = filter return p e in
     cond, with_eq (Zaux.eqmake (EQeq(Zaux.varpat id ty, e))) return
  | Etypeconstraintpat(p, _), _ -> filter return p e
  | Eorpat(p1, p2), _ ->
     let cond1, return = filter return p1 e in
     let cond2, return = filter return p2 e in
     or_op cond1 cond2, return
  | Erecordpat(l_p_list), _ ->
      (* { l1 = p1; ...; ln = pn } = e *)
      (* has the meaning of p1 = e.l1 ... pn = e.ln *)
      let cond, return =
       List.fold_left
	 (fun (cond, return) (l, p) ->
           let cond_l_p, return =
             filter return p (Zaux.record_access e l p.p_typ) in
	   and_op cond cond_l_p, return)
         (etrue, return) l_p_list in
     cond, return

and filter_list return p_list e_list =
  List.fold_left2
    (fun (cond, return) p e ->
      let cond_p_e, return = filter return p e in
      and_op cond cond_p_e, return) (Zaux.etrue, return)
    p_list e_list

(** In case a pattern matching is "simple", that is, *)
(* it is of the form P1 -> B1 | ... | Pn where the Pi are constructors *)
let is_a_case_statement p_h_list =
  let is_constr0pat { m_pat = { p_desc = p_desc } } =
    match p_desc with | Econstr0pat _ -> true | _ -> false in
  List.for_all is_constr0pat p_h_list
  
(** Translate a pattern matching construct into a conditional *)
(*- [match e with p1 -> B1 | ... | pn -> Bn] => 
 *- [c1 -> local ... B1 | ... | cn -> local ... Bn] *)
let match_into_condition total return e p_h_list =
  let rec conditional return p_h_list =
    match p_h_list with
    | [] -> assert false
    | [{ m_pat = p; m_body = b; m_env = env }] ->
        let cond, return = filter (with_env env return) p e in
        if !total then Zaux.eq_block b, return
        else Zaux.eq_ifthen cond b, return
    | { m_pat = p; m_body = b; m_env = env } :: p_h_list ->
        let cond, return = filter (with_env env return) p e in
        let b_else, return = conditional return p_h_list in
        Zaux.eq_ifthenelse cond b
          (Zaux.make_block Ident.Env.empty [b_else]), return in
  conditional return p_h_list
  

(* translate expressions *)
let rec expression ({ e_desc = desc } as e) =
  match desc with
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e
  | Eapp(app, e_arg, e_list) ->
      { e with e_desc = Eapp(app, expression e_arg,
                             List.map expression e_list) }
  | Eop(op, e_list) -> { e with e_desc = Eop(op, List.map expression e_list) }
  | Erecord_access(e, lid) ->
      { e with e_desc = Erecord_access(expression e, lid) }
  | Erecord(l_e_list) ->
      { e with e_desc =
                 Erecord (List.map (fun (l, e) -> (l, expression e)) l_e_list) }
  | Etypeconstraint(e, ty) ->
      { e with e_desc = Etypeconstraint(expression e, ty) }
  | Etuple(e_list) ->
      { e with e_desc = Etuple(List.map expression e_list) }
  | Econstr1 _ | Ematch _ | Eseq _ | Elet _ | Eperiod _ | Eblock _ | Epresent _
    -> assert false
    
let rec equation return ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(p, e) ->
      { eq with eq_desc = EQeq(p, expression e) }, return
  | EQinit(x, e) ->
     { eq with eq_desc = EQinit(x, expression e) }, return
  | EQreset(eq_list, e) ->
      let eq_list, return = Misc.map_fold equation return eq_list in
      { eq with eq_desc= EQreset(eq_list, expression e) }, return
  | EQmatch(total, e, p_h_list) ->
      let e = expression e in
      let p_h_list =
        List.map
          (fun ({ m_body = b } as h) -> { h with m_body = block b })
          p_h_list in
      if is_a_case_statement p_h_list
      then { eq with eq_desc = EQmatch(total, e, p_h_list) }, return
      else match_into_condition total return e p_h_list
  | EQnext _ | EQblock _ | EQemit _ | EQautomaton _
  | EQpresent _ | EQder _ | EQpluseq _
  | EQand _| EQbefore _| EQforall _-> assert false

and block ({ b_body = eq_list; b_env = b_env } as b) =
  let eq_list, { eqs = eqs; env = env } =
    Misc.map_fold equation empty eq_list in
  let env =
    State.fold
      (fun env acc -> Env.append env acc) env b_env in
  let eq_list = State.list eq_list eqs in
  Zaux.extend_block env eq_list b

let local ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, { eqs = eqs; env = env } =
    Misc.map_fold equation empty eq_list in
  let env =
    State.fold
      (fun env acc -> Env.append env acc) env l_env in
  let eq_list = State.list eq_list eqs in
  Zaux.extend_local env eq_list l

(* translate a top level expression *)
let let_expression ({ e_desc = desc } as e) =
  match desc with
  | Elet(l, e) -> { e with e_desc = Elet(local l, expression e) }
  | _ -> expression e

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
  | Efundecl(n, ({ f_body = e } as body)) ->
      { impl with desc = Efundecl(n, { body with f_body = let_expression e }) }
               
let implementation_list impl_list = List.map implementation impl_list
 
