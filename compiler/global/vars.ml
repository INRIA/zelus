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
        
let fv_block fv_local fv_body bounded acc
    { b_env = b_env; b_locals = l_list; b_body = body; b_write = defnames } =
  let bounded = names bounded b_env in
  let bounded = Deftypes.names bounded defnames in
  let bounded, acc = List.fold_left fv_local (bounded, acc) l_list in
  fv_body (names bounded b_env) acc body

let fv_match_handler fv_body m_h_list bounded acc = 
  List.fold_left
    (fun acc { m_pat = pat; m_body = b; m_env = env } ->
      fv_body (names bounded env) acc b)
    acc m_h_list

let operator acc = function
  | Eafter(n_list) -> List.fold_left (fun acc n -> S.add n acc) acc n_list
  | Efby | Eunarypre | Eifthenelse | Etest 
  | Eminusgreater | Eup | Einitial | Edisc | Ehorizon | Eop _ | Eevery _ -> acc
	   
let rec fv bounded (last_acc, acc) e =
  match e.e_desc with
  | Etuple(e_list) -> List.fold_left (fv bounded) (last_acc, acc) e_list
  | Eapp(op, e_list) ->
     List.fold_left (fv bounded) (last_acc, operator acc op) e_list
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
  | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> last_acc, acc
  | Epresent _ | Ematch _ -> assert false
        
and fv_eq bounded (last_acc, acc) { eq_desc = desc; eq_write = w } =
  match desc with
    | EQeq(_, e) | EQinit(_, e) | EQpluseq(_, e) -> fv bounded (last_acc, acc) e
    | EQmatch(_, e, m_h_list) ->
       fv_match_handler (fv_block fv_local fv_eq_list) m_h_list bounded 
			(fv bounded (last_acc, acc) e)
    | EQreset(eq_list, r) ->
       (* remove the names written in the body *)
       fv bounded
	  (fv_eq_list (Deftypes.names bounded w) (last_acc, acc) eq_list) r
    | EQder(_, e, None, []) -> fv bounded (last_acc, acc) e
    | EQblock(b) -> fv_block fv_local fv_eq_list bounded (last_acc, acc) b
    | EQder _ | EQemit _ | EQpresent _  
    | EQautomaton _ | EQnext _ -> assert false

and fv_eq_list bounded acc eq_list = List.fold_left (fv_eq bounded) acc eq_list

and fv_local (bounded, acc) { l_eq = eq_list; l_env = l_env } =
  let acc = List.fold_left (fv_eq (names bounded l_env)) acc eq_list in
  (bounded, acc)

let fv acc e =
  let acc_last, acc = fv S.empty (S.empty, acc) e in S.union acc_last acc

(** The main entries *)
let rec init { eq_desc = desc } =
  match desc with
  | EQinit _ -> true
  | EQreset(eq_list, _) -> List.for_all init eq_list
  | _ -> false

let read eq = fv_eq S.empty (S.empty, S.empty) eq
let def { eq_write = { Deftypes.dv = dv; Deftypes.di = di } } =
  (* derivatives are not taken into account *)
  S.union dv di
let nodep ({ eq_desc }) =
  match eq_desc with
  | EQeq(_, { e_desc = Eapp(Eup, _) })
  | EQder(_, _, None, []) -> true | _ -> false
