(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
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
                      (* [x1\y1,..., xn\yn] *)
                      (* after an equation [next yk = e], entry [xk\yk] *)
                      (* cannot be applied anymore *)
                      
let empty = { renaming = Env.empty; captured = S.empty }

(** Closure of a relation. If [x1\x2, x2\x3] => [x1\x3, x2\x3] *)
(* The implementation is poor: replace it by the classical union-find *)
let closure ({ renaming = rel } as r) = 
  (* [closure rel n = rel, m] returns a new renaming and *)
  (* the associated name [m] to [n] so that there is no link [m\k] *)
  let rec closure n = 
    try
      let m = Env.find n rel in
      closure m
    with Not_found -> n in
  { r with 
    renaming = Env.fold (fun n _ acc -> Env.add n (closure n) acc) rel Env.empty }

(** Apply the renaming *)
let rename n { renaming = renaming; captured = captured } = 
  try 
    let m = Env.find n renaming in
    if S.mem m captured then n else m
  with Not_found -> n

(** Build a substitution [x1\y1,...,xn\yn]. Do not take variables *)
(** from w (set of writes) *)
let rec build w ({ renaming = renaming } as r) { eq_desc = desc } =
  match desc with
    | EQeq({ p_desc = Evarpat(n) }, { e_desc = Elocal(m) }) when not (S.mem n w) ->
        { r with renaming = Env.add n m renaming }
    | EQeq _ | EQset _ | EQnext _ | EQinit _ | EQmatch _ | EQreset _ 
    | EQder(_, _, None, []) -> r
    | EQautomaton _ | EQpresent _ | EQemit _ | EQder _ | EQblock _ -> assert false

(** Treating an expression. Apply the renaming substitution recursively *)
let rec expression renaming ({ e_desc = desc } as e) =
  match desc with
    | Econst _ | Econstr0 _ | Eglobal _ | Elast _ -> e
    | Elocal(n) -> { e with e_desc = Elocal(rename n renaming) }
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (expression renaming) e_list) }
    | Erecord(n_e_list) -> 
        { e with e_desc =
		   Erecord(List.map (fun (ln, e) ->
				     (ln, expression renaming e)) n_e_list) }
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
    | Eperiod _ | Epresent _ | Ematch _ -> assert false

(** Renaming a local declaration *)
and local renaming ({ l_eq = eq_list } as l) =
  let renaming = 
    List.fold_left (build S.empty) renaming eq_list in
  let renaming = closure renaming in
  let renaming, eq_list = equation_list renaming eq_list in
  renaming, { l with l_eq = eq_list }

(** renaming of equations *)
and equation (renaming, eq_list) ({ eq_desc = desc } as eq) =
    match desc with
    | EQnext(n, e, e_opt) ->
       { renaming with captured = S.add n renaming.captured },
       { eq with eq_desc = 
		   EQnext(n, expression renaming e,
			  Misc.optional_map (expression renaming) e_opt) } 
       :: eq_list 
    | EQeq(p, e) -> 
       renaming, { eq with eq_desc = EQeq(p, expression renaming e) } :: eq_list
    | EQset(ln, e) ->
       renaming, 
       { eq with eq_desc = EQset(ln, expression renaming e) } :: eq_list
    | EQinit(n, e0) ->
       renaming, 
       { eq with eq_desc = EQinit(n, expression renaming e0) } :: eq_list
    | EQmatch(total, e, m_b_list) ->
       let rename ({ m_body = b } as m_h) =
         { m_h with m_body = block renaming b } in
       let e = expression renaming e in
       renaming,
       { eq with eq_desc = EQmatch(total, e, 
				   List.map rename m_b_list) } :: eq_list
    | EQder(n, e, None, []) ->
       renaming, 
       { eq with eq_desc = EQder(n, expression renaming e, None, []) } :: eq_list
    | EQreset(res_eq_list, e) ->
       let e = expression renaming e in
       let renaming, res_eq_ist = equation_list renaming res_eq_list in
       renaming, { eq with eq_desc = EQreset(res_eq_list, e) } :: eq_list
    | EQautomaton _ | EQpresent _ 
    | EQemit _ | EQder _ | EQblock _ -> assert false

and equation_list renaming eq_list =
  let renaming, eq_list = List.fold_left equation (renaming, []) eq_list in
  renaming, List.rev eq_list

and block renaming ({ b_env = b_env; b_body = eq_list; b_write = { dv = w } } as b) =
  let renaming = List.fold_left (build w) renaming eq_list in
  let renaming = closure renaming in
  let _, eq_list = equation_list renaming eq_list in
  { b with b_body = eq_list }

let implementation impl =
  match impl.desc with
    | Efundecl(f, ({ f_body = e } as body)) ->
        let e = expression empty e in
        let body = { body with f_body = e } in
        { impl with desc = Efundecl(f, body) }
    | _ -> impl
        
let implementation_list impl_list = Misc.iter implementation impl_list
