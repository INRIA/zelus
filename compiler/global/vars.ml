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
(* free variables, defined variables and useful function *)
(* for traversing expressions *)

open Misc
open Ident
open Zelus

(* defined names in an environment *)
let names bounded env = Env.fold (fun n _ bounded -> S.add n bounded) env bounded

let rec fv_pat bounded acc p =
  match p.p_desc with
    | Ewildpat | Econstr0pat _ | Econstpat _ -> acc
    | Evarpat(x) -> 
        if (S.mem x acc) || (S.mem x bounded) then acc else S.add x acc
    | Etuplepat(pat_list) -> List.fold_left (fv_pat bounded) acc pat_list
    | Erecordpat(label_pat_list) ->
        List.fold_left (fun acc (_, p) -> fv_pat bounded acc p) acc label_pat_list
    | Ealiaspat(p, name) ->
        let acc = 
	  if (S.mem name acc) || (S.mem name bounded)
	  then acc else S.add name acc in
          fv_pat bounded acc p
    | Eorpat(p1, _) -> fv_pat bounded acc p1
    | Etypeconstraintpat(p, _) -> fv_pat bounded acc p
        
let fv_block fv_local fv_body bounded acc { b_env = b_env; b_body = body } =
  fv_body (names bounded b_env) acc body
 
let fv_match_handler fv_body m_h_list bounded acc = 
  List.fold_left
    (fun acc { m_pat = pat; m_body = b; m_env = env } ->
      fv_body (names bounded env) acc b)
    acc m_h_list
 
let rec fv bounded (last_acc, acc) e =
  match e.e_desc with
    | Etuple(e_list) 
    | Eapp(_, e_list) -> List.fold_left (fv bounded) (last_acc, acc) e_list
    | Elocal(n) ->
       last_acc, if (S.mem n acc) || (S.mem n bounded) then  acc else S.add n acc
    | Elast(n) ->
       (if (S.mem n last_acc) || (S.mem n bounded) 
	then last_acc else S.add n last_acc), acc
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> fv bounded (last_acc, acc) e
    | Erecord(f_e_list) ->
       List.fold_left (fun acc (_, e) -> fv bounded acc e) (last_acc, acc) f_e_list
    | Elet(local, e) ->
       let bounded, acc = fv_local (bounded, (last_acc, acc)) local in
       fv bounded acc e
    | Eseq(e1, e2) -> fv bounded (fv bounded (last_acc, acc) e1) e2
    | Econst _ | Econstr0 _ | Eglobal _ -> last_acc, acc
    | Epresent _ | Ematch _ | Eperiod _ -> assert false
        
and fv_eq bounded (last_acc, acc) { eq_desc = desc; eq_after = w } =
  let last_acc, acc =
    match desc with
    | EQeq(_, e) | EQinit(_, e) | EQset(_, e) -> fv bounded (last_acc, acc) e
    | EQmatch(_, e, m_h_list) ->
       fv_match_handler (fv_block fv_local fv_eq_list) m_h_list bounded 
			(fv bounded (last_acc, acc) e)
    | EQreset(eq_list, r) ->
       fv_eq_list bounded (fv bounded (last_acc, acc) r) eq_list
    | EQder(_, e, None, []) -> fv bounded (last_acc, acc) e
    | EQblock _ | EQder _ | EQemit _ | EQpresent _  
    | EQautomaton _ | EQnext _ -> assert false in
  last_acc, S.union acc (S.diff w bounded)

and fv_eq_list bounded acc eq_list = List.fold_left (fv_eq bounded) acc eq_list

and fv_local (bounded, acc) { l_eq = eq_list; l_env = l_env } =
  let acc = List.fold_left (fv_eq (names bounded l_env)) acc eq_list in
  (bounded, acc)

and build bounded acc { eq_desc = desc; eq_before = before } =
  let block bounded acc { b_body = eq_list; b_env = b_env } = 
    List.fold_left (build (names bounded b_env)) acc eq_list in
  let acc =
    match desc with
    | EQeq(pat, _) -> fv_pat bounded acc pat
    | EQinit(n, _) ->
       if (S.mem n acc) || (S.mem n bounded) then acc else S.add n acc
    | EQreset(eq_list, _) -> build_list bounded acc eq_list
    | EQmatch(_, _, m_h_list) ->
        List.fold_left 
          (fun acc { m_body = b_eq_list } -> 
	   block bounded acc b_eq_list) acc m_h_list
    | EQder(_, _, None, []) | EQset _ -> acc
    | EQblock _ | EQder _ | EQautomaton _ 
    | EQpresent _ | EQemit _ | EQnext _ -> assert false in
  S.union acc (S.diff before bounded)
	  
and build_list bounded acc eq_list = List.fold_left (build bounded) acc eq_list

(** The main entries *)
let rec init { eq_desc = desc } =
  match desc with
  | EQinit _ -> true
  | EQreset([eq], _) -> init eq
  | _ -> false

let fv acc e =
  let acc_last, acc = fv S.empty (S.empty, acc) e in S.union acc_last acc

let read eq = fv_eq S.empty (S.empty, S.empty) eq
let def eq = build S.empty S.empty eq
let defs eq_list = List.fold_left (build S.empty) S.empty eq_list
let rec antidep { eq_desc = desc } =
  match desc with
    | EQeq(_, { e_desc = Eapp((Eunarypre | Efby | Eup), _) }) | EQnext _ -> true
    | _ -> false
