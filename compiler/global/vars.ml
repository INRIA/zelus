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
(* free variables, defined variables and useful function *)
(* for traversing expressions *)

open Misc
open Ident
open Zelus

let rec fv_pat acc p =
  match p.p_desc with
    | Ewildpat | Econstr0pat _ | Econstpat _ -> acc
    | Evarpat(x) -> 
        if S.mem x acc then acc else S.add x acc
    | Etuplepat(pat_list) -> List.fold_left fv_pat acc pat_list
    | Erecordpat(label_pat_list) ->
        List.fold_left (fun acc (_, p) -> fv_pat acc p) acc label_pat_list
    | Ealiaspat(p, name) ->
        let acc = if S.mem name acc then acc else S.add name acc in
          fv_pat acc p
    | Eorpat(p1, _) -> fv_pat acc p1
    | Etypeconstraintpat(p, _) -> fv_pat acc p
        
let fv_block fv_local fv_body bounded acc 
    { b_vars = n_list; b_locals = l; b_body = body } =
  let bounded, acc = List.fold_left fv_local (bounded, acc) l in
  let bounded = 
    List.fold_left 
      (fun bounded n -> if S.mem n bounded then bounded else S.add n bounded)
      bounded n_list in
  fv_body bounded acc body
 
let fv_match_handler fv_body m_h_list bounded acc = 
  List.fold_left
    (fun acc { m_pat = pat; m_body = b } ->
      let bounded = fv_pat bounded pat in
      fv_body bounded acc b)
    acc m_h_list
 
let rec fv bounded acc e =
  match e.e_desc with
    | Etuple(e_list) | Eapp(_, e_list) -> 
        List.fold_left (fv bounded) acc e_list
    | Elocal(n) ->
        if (S.mem n acc) || (S.mem n bounded) then acc else S.add n acc
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> fv bounded acc e
    | Erecord(f_e_list) ->
        List.fold_left (fun acc (_, e) -> fv bounded acc e) acc f_e_list
    | Elet(local, e) ->
        let bounded, acc = fv_local (bounded, acc) local in
          fv bounded acc e
    | Eseq(e1, e2) -> fv bounded (fv bounded acc e1) e2
    | Elast _ | Econst _ | Econstr0 _ 
    | Eglobal _ | Eperiod _ | Epresent _ | Ematch _ -> acc
        
and fv_eq bounded acc eq =
  match eq.eq_desc with
    | EQeq(_, e) | EQinit(_, e, None) | EQnext(_, e, None) -> fv bounded acc e
    | EQinit(_, e, e_opt) | EQnext(_, e, e_opt)-> 
        fv bounded (Misc.optional (fv bounded) acc e_opt) e
    | EQmatch(_, e, m_h_list) ->
        fv_match_handler (fv_block fv_local fv_eq_list) m_h_list bounded 
	  (fv bounded acc e)
    | EQreset(b_eq_list, r) ->
        fv_block fv_local fv_eq_list bounded (fv bounded acc r) b_eq_list
    | EQder _ | EQemit _  
    | EQpresent _  | EQautomaton _ -> assert false

and fv_eq_list bounded = List.fold_left (fv_eq bounded)

and build bounded eq =
  let one_handler acc { b_body = eq_list } = List.fold_left build acc eq_list in
  match eq.eq_desc with
    | EQeq(pat, _) | EQinit(pat, _, _) | EQnext(pat, _, _) -> fv_pat bounded pat
    | EQreset(b, e) ->
        one_handler bounded b
    | EQmatch(_, _, m_h_list) ->
        List.fold_left 
          (fun acc { m_body = b } -> one_handler acc b) bounded m_h_list
    | EQder _ | EQautomaton _ | EQpresent _ | EQemit _ -> 
        assert false
                
and fv_local (bounded, acc) { l_eq = eq_list } =
  let bounded = List.fold_left build bounded eq_list in
  let acc = List.fold_left (fv_eq bounded) acc eq_list in
  (bounded, acc)

(** The main entries *)
let read eq = fv_eq S.empty S.empty eq
let def eq = build S.empty eq
let defs eq_list = List.fold_left build S.empty eq_list
let antidep eq =
  match eq.eq_desc with
    | EQeq(_, { e_desc = Eapp((Eunarypre | Efby), _) }) | EQnext _ -> true
    | _ -> false
