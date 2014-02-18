(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* Elimination of copy variables [x = y] *)
(* The transformation is applied after static scheduling and before *)
(* translation into sequential code *)

open Misc
open Ident
open Zelus
open Deftypes

type renaming =
    { renaming: Ident.t Env.t; (* the substitution *)
      captured: S.t } (* names from this set are not renamed *)
                      (* after an equation [x = v fby e], [x] cannot be substituted *)
                      
let empty = { renaming = Env.empty; captured = S.empty }

(** Apply the renaming *)
let rename n { renaming = renaming; captured = captured } = 
  try 
    let m = Env.find n renaming in
    if S.mem m captured then n else m
  with Not_found -> n

(** Build a substitution. Remove copy equations [y = x]. Do not take variables *)
(** from w (set of writes) *)
let build w ({ renaming = renaming } as r) { eq_desc = desc } =
  match desc with
    | EQeq({ p_desc = Evarpat(n) }, { e_desc = Elocal(m) }) when not (S.mem n w) ->
        { r with renaming = Env.add n m renaming }
    | EQeq _ | EQnext _ | EQinit _ | EQmatch _ | EQreset _ -> r
    | EQautomaton _ | EQpresent _ | EQemit _ 
    | EQder _ -> assert false

(** Treating an expression. Apply the renaming substitution recursively *)
let rec expression renaming ({ e_desc = desc } as e) =
  match desc with
    | Econst _ | Econstr0 _ | Eglobal _ -> e
    | Elocal(n) -> { e with e_desc = Elocal(rename n renaming) }
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (expression renaming) e_list) }
    | Erecord(n_e_list) -> 
        { e with e_desc =
            Erecord(List.map (fun (ln, e) -> (ln, expression renaming e)) n_e_list) }
    | Erecord_access(e, ln) ->
        { e with e_desc =
            Erecord_access(expression renaming e, ln) }
    | Eapp(op, e_list) ->
        { e with e_desc = Eapp(op, List.map (expression renaming) e_list) }
    | Etypeconstraint(e1, ty) -> 
        { e with e_desc = Etypeconstraint(expression renaming e1, ty) }      
    | Eseq(e1, e2) ->
        { e with e_desc = Eseq(expression renaming e1, expression renaming e2) }
    | Elet(l, e_let) ->
        let renaming, l = local renaming l in
        let e_let = expression renaming e_let in
        begin match l.l_eq with 
          | [] -> e_let | _ -> { e with e_desc = Elet(l, e_let) } end
    | Eperiod _ | Elast _ | Epresent _ | Ematch _ -> assert false

(** Renaming a local declaration *)
and local renaming ({ l_eq = eq_list } as l) =
  let renaming = 
    List.fold_left (build S.empty) renaming eq_list in
  let eq_list = equation_list renaming eq_list in
  renaming, { l with l_eq = eq_list }

(** renaming of equations *)
and equation (renaming, eq_list) ({ eq_desc = desc } as eq) =
    match desc with
      | EQeq(({ p_desc = Evarpat(n) } as p), 
	     ({ e_desc = Eapp((Eunarypre | Efby), e_list) } as e)) ->
	  (* The substitution [n/m] is removed from the environment *)
	  (* E.g., [y/x] applied to y = 0 fby x; k = x + 2 *)
	  { renaming with captured = S.add n renaming.captured },
	  { eq with eq_desc = EQeq(p, expression renaming e) } :: eq_list 
      | EQeq(p, e) -> 
	  renaming, { eq with eq_desc = EQeq(p, expression renaming e) } :: eq_list
      | EQmatch(total, e, m_b_list) ->
          let rename ({ m_body = b } as m_h) =
            { m_h with m_body = block renaming b } in
          let e = expression renaming e in
          renaming,
	  { eq with eq_desc = EQmatch(total, e, 
				      List.map rename m_b_list) } :: eq_list
      | EQreset _ | EQautomaton _ | EQpresent _ 
      | EQemit _ | EQinit _ | EQnext _ | EQder _ -> assert false

and equation_list renaming eq_list =
  let renaming, eq_list = List.fold_left equation (renaming, []) eq_list in
  List.rev eq_list

and block renaming ({ b_body = eq_list; b_write = { dv = w } } as b) =
  let renaming = List.fold_left (build w) renaming eq_list in
  let eq_list = equation_list renaming eq_list in
  { b with b_body = eq_list }

let implementation impl =
  match impl.desc with
    | Efundecl(f, ({ f_body = e } as body)) ->
        let e = expression empty e in
        let body = { body with f_body = e } in
        { impl with desc = Efundecl(f, body) }
    | _ -> impl
        
let implementation_list impl_list = Misc.iter implementation impl_list
