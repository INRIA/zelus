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

(* safe/unsafe expressions and equations. *)
(* A computation is safe when it is combinatorial, that is, it *)
(* has no side effect, total and no state *)
open Zelus
open Ident
open Deftypes
open Zaux
       
(** An expression or equation is unsafe if it contains an unsafe operation. *)
let rec exp { e_desc = desc } =
  match desc with
  | Eapp(_, e, e_list) ->
     (* look if (e e1...en) is combinatorial *)
     (not (Types.is_combinatorial (List.length e_list) e.e_typ))
     || (exp e) || (List.exists exp e_list)
  | Erecord_access(e, _) | Etypeconstraint(e, _) -> exp e
  | Erecord(f_e_list) ->
     List.exists (fun (_, e) -> exp e) f_e_list
  | Erecord_with(e, f_e_list) ->
     exp e || List.exists (fun (_, e) -> exp e) f_e_list
  | Eseq(e1, e2) -> (exp e1) || (exp e2)
  | Elocal _ | Elast _ | Econst _ | Econstr0 _ 
  | Eglobal _ | Eperiod _ | Eop _ -> false
  | Elet _ | Eblock _ -> true
  | Econstr1(_, e_list) | Etuple(e_list) -> List.exists exp e_list
  | Epresent _ | Ematch _ -> assert false
				    
let rec equation { eq_desc = desc } =
  match desc with
  | EQeq(_, e) | EQinit(_, e) | EQder(_, e, None, []) | EQpluseq(_, e) -> exp e
  | EQmatch(_, e, m_h_list) ->
     exp e
     || List.exists
	  (fun { m_body = b_eq_list } -> block_eq_list b_eq_list) m_h_list
  | EQreset(eq_list, e) ->
     exp e || List.exists equation eq_list
  | EQand(eq_list)
  | EQbefore(eq_list) -> List.exists equation eq_list
  | EQforall
      { for_index = i_list; for_init = init_list; for_body = b_eq_list } ->
     let index { desc = desc } =
       match desc with
       | Einput(_, e) -> exp e
       | Eoutput _ -> false
       | Eindex(_, e1, e2) -> exp e1 || exp e2 in
     let init { desc = desc } =
       match desc with
       | Einit_last(_, e) -> exp e in
     List.exists index i_list ||
       List.exists init init_list ||
	 block_eq_list b_eq_list
  | EQder _ | EQnext _ | EQautomaton _
  | EQpresent _ | EQemit _ | EQblock _ -> assert false

and block_eq_list { b_locals = l_list; b_body = eq_list } =
  (List.exists (fun { l_eq = eq_list } -> List.exists equation eq_list) l_list)
  || List.exists equation eq_list
