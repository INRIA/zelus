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

(** Simple cost function for an expression *)
(** [max] is the maximum allowed cost of [e] *)
(** raise Exit if the cost is greater than [max]      *)
(** continuous operators (up/der) reduce the local cost *)
(** since calling a function with continuous state need extra copy code *)

open Misc
open Ident
open Lident
open Global
open Zelus
open Zaux

let expression e max =
  let c = ref 0 in
  let incr n =
    let c' = !c + n in
      if c' >= max then raise Exit
      else c := !c + n in
  let rec cost e =
    match e.e_desc with
      | Elocal _ | Elast _ | Econst _ | Econstr0 _ | Eglobal _ -> ()
      | Eapp(_, e, e_list) ->
         incr (1 + List.length e_list);
	 List.iter cost e_list; cost e
      | Econstr1(_, e_list) | Etuple(e_list) -> incr 1; List.iter cost e_list
      | Eop(op, e_list) -> incr (cost_op op); List.iter cost e_list
      | Erecord(n_e_list) ->
	 incr 1; List.iter (fun (label, e) -> cost e) n_e_list
      | Erecord_access(e, _) -> cost e
      | Erecord_with(e, n_e_list) ->
	 cost e; incr 1; List.iter (fun (label, e) -> cost e) n_e_list
      | Eseq(e1, e2) -> cost e1; cost e2
      | Eperiod({ p_phase = p1_opt; p_period = p2 }) -> 
          incr 1; ignore (Misc.optional_map cost p1_opt); cost p2
      | Etypeconstraint(e, _) -> cost e
      | Elet(local, e_let) ->
          cost_local local; cost e_let
      | Eblock(b, e_block) ->
	 cost_block b; cost e_block
      | Epresent _ | Ematch _ -> assert false
  and cost_op op = 
    match op with 
    | Efby | Eunarypre | Eminusgreater -> 2
    | Edisc -> 4
    | Einitial -> 2
    | Eup -> -2
    | Eifthenelse
    | Etest
    | Eaccess -> 1
    | Ehorizon -> 1
    | Eupdate | Eslice _ | Econcat -> 1
    | Eatomic -> 0
  (* this is rough: after specialization, the size is known *)
  and cost_block { b_locals = l_list; b_body = eq_list } =
    List.iter cost_local l_list; List.iter cost_eq eq_list
  and cost_local { l_eq = eq_list } =
    List.iter cost_eq eq_list
  and cost_eq eq =
    match eq.eq_desc with
      | EQeq(_, e) | EQinit(_, e) | EQpluseq(_, e) -> incr 1; cost e
      | EQnext(_, e0, e_opt) -> 
	  incr 1; cost e0; Misc.optional_unit (fun _ e -> cost e) () e_opt
      | EQmatch(_, e, p_h_list) ->
          cost e;
          List.iter (fun { m_body = b } -> cost_block b) p_h_list
      | EQder(n, e, e0_opt, h) ->
          incr (-2);
          Misc.optional_unit (fun _ e -> cost e) () e0_opt;
          List.iter (fun { p_body = e } -> cost e) h;
          cost e
      | EQreset(eq_list, e) -> incr 1; List.iter cost_eq eq_list
      | EQand(eq_list)
      | EQbefore(eq_list) -> List.iter cost_eq eq_list
      | EQpresent(p_h_list, b_opt) ->
	  List.iter (fun { p_body = b } -> cost_block b) p_h_list;
	  Misc.optional_unit (fun _ b -> cost_block b) () b_opt
      | EQemit(_, e_opt) ->
	  Misc.optional_unit (fun _ e -> cost e) () e_opt
      | EQblock(b) -> cost_block b
      | EQforall { for_index = i_list; for_init = init_list;
		   for_body = b_eq_list } ->
	 let index { desc = desc } =
	   match desc with
	   | Einput(_, e) -> incr 1; cost e
	   | Eoutput _ -> incr 1
	   | Eindex(_, e1, e2) -> incr 1; cost e1; cost e2 in
	 let init { desc = desc } =
	   match desc with
	   | Einit_last(_, e) -> incr 1; cost e in
	 List.iter index i_list;
	 List.iter init init_list;
	 incr (List.length i_list);
	 cost_block b_eq_list
      | EQautomaton(_, s_h_list, se_opt) ->
	 List.iter cost_state_handler s_h_list;
	 Misc.optional_unit (fun _ se -> cost_state_exp se) () se_opt	 
  and cost_state_handler { s_body = b; s_trans = esc_list } =
    cost_block b; List.iter cost_escape esc_list
  and cost_escape { e_cond = scpat; e_block = b_opt; e_next_state = se } =
    cost_scpat scpat;
    Misc.optional_unit (fun _ b -> cost_block b) () b_opt;
    cost_state_exp se
  and cost_state_exp { desc = desc } =
    match desc with
    | Estate0 _ -> incr 1
    | Estate1(_, e_list) -> List.iter cost e_list
  and cost_scpat { desc = desc } =
    match desc with
    | Econdand(scpat1, scpat2)
    | Econdor(scpat1, scpat2) -> cost_scpat scpat1; cost_scpat scpat2
    | Econdexp(e) | Econdpat(e, _) -> cost e
    | Econdon(scpat, e) -> cost_scpat scpat; cost e
    
  in
  try
    cost e; true
  with
    | Exit -> false
