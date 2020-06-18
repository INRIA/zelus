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

(* free variables, defined variables *)

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
    | Econstr1pat(_, pat_list) | Etuplepat(pat_list) ->
        List.fold_left (fv_pat bounded) acc pat_list
    | Erecordpat(label_pat_list) ->
        List.fold_left
          (fun acc (_, p) -> fv_pat bounded acc p) acc label_pat_list
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
  let bounded, acc = List.fold_left fv_local (bounded, acc) l_list in
  bounded, fv_body bounded acc body

let fv_match_handler fv_body m_h_list bounded acc = 
  List.fold_left
    (fun acc { m_pat = pat; m_body = b; m_env = env } ->
      fv_body (names bounded env) acc b)
    acc m_h_list

let rec size acc { desc = desc } =
  match desc with
  | Sconst _ | Sglobal _ -> acc
  | Sname(n) -> S.add n acc
  | Sop(_, s1, s2) -> size (size acc s1) s2
                           
let operator acc = function
  | Efby | Eunarypre | Eifthenelse | Etest 
    | Eminusgreater | Eup | Einitial | Edisc
    | Ehorizon | Eaccess | Eupdate | Econcat | Eatomic -> acc
    | Eslice(s1, s2) -> size (size acc s1) s2
	   
let rec fv bounded (last_acc, acc) e =
  match e.e_desc with
  | Eop(op, e_list) ->
     let last_acc, acc = List.fold_left (fv bounded) (last_acc, acc) e_list in
     last_acc, operator acc op
  | Econstr1(_, e_list) | Etuple(e_list) ->
      List.fold_left (fv bounded) (last_acc, acc) e_list
  | Eapp(_, e, e_list) ->
     List.fold_left (fv bounded) (fv bounded (last_acc, acc) e) e_list
  | Elocal(n) ->
     last_acc, if (S.mem n acc) || (S.mem n bounded) then  acc else S.add n acc
  | Elast(n) ->
     (if (S.mem n last_acc) || (S.mem n bounded) 
      then last_acc else S.add n last_acc), acc
  | Erecord_access(e, _) | Etypeconstraint(e, _) ->
      fv bounded (last_acc, acc) e
  | Erecord(f_e_list) ->
     List.fold_left
       (fun acc (_, e) -> fv bounded acc e) (last_acc, acc) f_e_list
  | Erecord_with(e, f_e_list) ->
     let last_acc, acc = fv bounded (last_acc, acc) e in
     List.fold_left
       (fun acc (_, e) -> fv bounded acc e) (last_acc, acc) f_e_list
  | Elet(local, e) ->
     let bounded, acc = fv_local (bounded, (last_acc, acc)) local in
     fv bounded acc e
  | Eblock(b, e) ->
     let acc = fv_block_eq_list bounded (last_acc, acc) b in fv bounded acc e
  | Eseq(e1, e2) -> fv bounded (fv bounded (last_acc, acc) e1) e2
  | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> last_acc, acc
  | Epresent _ | Ematch _ -> assert false
        
and fv_eq bounded (last_acc, acc) { eq_desc = desc } =
  match desc with
  | EQeq(_, e) | EQinit(_, e) | EQpluseq(_, e) ->
				 fv bounded (last_acc, acc) e
  | EQmatch(_, e, m_h_list) ->
     fv_match_handler fv_block_eq_list m_h_list bounded 
		      (fv bounded (last_acc, acc) e)
  | EQreset(eq_list, r) ->
     fv bounded (fv_eq_list bounded (last_acc, acc) eq_list) r
  | EQder(_, e, None, []) -> fv bounded (last_acc, acc) e
  | EQblock(b) -> fv_block_eq_list bounded (last_acc, acc) b
  | EQand(eq_list)
  | EQbefore(eq_list) -> fv_eq_list bounded (last_acc, acc) eq_list
  | EQforall { for_index = i_list; for_init = init_list;
	       for_body = b_eq_list } ->
     (* read variables from the expression in the list of indexes *)
     (* [i in e0 .. e1], [xi in e], [xo out e] *)
     let index (last_acc, acc) { desc = desc } =
       match desc with
       | Einput(_, e) -> fv bounded (last_acc, acc) e
       | Eindex(_, e1, e2) ->
	  fv bounded (fv bounded (last_acc, acc) e1) e2
       | Eoutput _ -> last_acc, acc in
     (* read variables from the initialized variables *)
     (* last x = e removes last x from the list of read variables *)
     let init (bounded, last_acc, acc) { desc = desc } =
       match desc with
       | Einit_last(x, e) ->
	  let last_acc, acc = fv bounded (last_acc, acc) e in
	  (S.add x bounded, last_acc, acc) in
     let last_acc, acc = List.fold_left index (last_acc, acc) i_list in
     let bounded, last_acc, acc =
       List.fold_left init (bounded, last_acc, acc) init_list in
     fv_block_eq_list bounded (last_acc, acc) b_eq_list
  | EQder _ | EQemit _ | EQpresent _  
  | EQautomaton _ | EQnext _ -> assert false

and fv_eq_list bounded acc eq_list = List.fold_left (fv_eq bounded) acc eq_list

and fv_local (bounded, acc) { l_eq = eq_list; l_env = l_env } =
  let bounded = names bounded l_env in
  let acc = List.fold_left (fv_eq bounded) acc eq_list in
  (bounded, acc)

and fv_block_eq_list bounded acc b =
  let _, acc = fv_block fv_local fv_eq_list bounded acc b in acc
					    
let fve acc e =
  let acc_last, acc = fv S.empty (S.empty, acc) e in S.union acc_last acc
