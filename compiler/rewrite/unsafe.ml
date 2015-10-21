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

open Zelus
open Ident
open Deftypes
open Zaux
       
(** An expression or equation is unsafe if it contains an unsafe operation. *)
let rec exp { e_desc = desc } =
  match desc with
    | Eapp((Eop(_, f) | Eevery(_, f)), _) when not (Types.is_a_safe_function f)
	-> true
    | Eapp(_, e_list) | Etuple(e_list) -> List.exists exp e_list
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> exp e
    | Erecord(f_e_list) ->
      List.exists (fun (_, e) -> exp e) f_e_list
    | Eseq(e1, e2) -> (exp e1) || (exp e2)
    | Elocal _ | Elast _ | Econst _ | Econstr0 _ 
    | Eglobal _ | Eperiod _ -> false
    | Elet _ -> true
    | Epresent _ | Ematch _ -> assert false
      
let rec equation { eq_desc = desc } =
  match desc with
    | EQeq(_, e) | EQinit(_, e) | EQder(_, e, None, []) | EQpluseq(_, e) -> exp e
    | EQmatch(_, e, m_h_list) ->
       exp e
       || List.exists
	    (fun { m_body = { b_locals = l_list; b_body = eq_list } } ->
	     (List.exists
		(fun { l_eq = eq_list } -> List.exists equation eq_list) l_list)
	     || List.exists equation eq_list) m_h_list
    | EQreset(eq_list, e) ->
       exp e || List.exists equation eq_list
    | EQder _ | EQnext _ | EQautomaton _
    | EQpresent _ | EQemit _ | EQblock _ -> assert false
