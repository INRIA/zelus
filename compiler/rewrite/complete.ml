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

(* complete branches with a default value [der x = 0.0] for state variables *)
(* This step is applied to normalised equations for which *)
(* read/write information is up-to-date *)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

(* Make an equation [x = e] *)
let eq x e = eqmake (EQeq(pmake (Evarpat(x)) e.e_typ, e))

let der_eq_zero x = eqmake (EQder(x, Zaux.zero, None, []))

(* complete a set of equations with default equations for every *)
(* variable from [eq_write] which is not defined in [eq_write_block] *)
let complete_eq_list { der = der } ({ der = der_l } as b_write_local) eq_list =
  let l = S.diff der der_l in
  let eq_list = S.fold (fun x acc -> (der_eq_zero x) :: acc) l eq_list in
  eq_list, { b_write_local with der = der }		       

let rec exp ({ e_desc } as e) = 
  let e_desc = match e_desc with
    | Elast _ | Elocal _ | Econst _ | Econstr0 _ | Eglobal _ -> e_desc
    | Etuple(e_list) ->
       Etuple (List.map exp e_list)
    | Econstr1(c, e_list) -> Econstr1(c, List.map exp e_list)
    | Eop(op, e_list) -> Eop(op, List.map exp e_list)
    | Eapp(app, e_op, e_list) ->
       let e_list = List.map exp e_list in
       Eapp(app, exp e_op, e_list)
    | Erecord(label_e_list) ->
       let label_e_list =
	 List.map (fun (l, e) -> (l, exp e)) label_e_list in
       Erecord(label_e_list)
    | Erecord_access(e_record, longname) ->
       Erecord_access(exp e_record, longname)
    | Erecord_with(e_record, label_e_list) ->
       let label_e_list =
	 List.map (fun (l, e) -> (l, exp e)) label_e_list in
       Erecord_with(exp e_record, label_e_list)
    | Etypeconstraint(e1, ty) ->
       Etypeconstraint(exp e1, ty)
    | Elet(l, e) -> 
       let l = local l in Elet(l, exp e)
    | Eseq(e1, e2) -> 
       Eseq(exp e1, exp e2)
    | Ematch(total, e, m_h_list) ->
        let e = exp e in
        let m_h_list = match_handler_exp_list m_h_list in
        Ematch(total, e, m_h_list)
    | Eblock(b, e) ->
        let b = block_eq_list b in
        Eblock(b, exp e)
    | Eperiod _ | Epresent _ -> assert false in
  { e with e_desc = e_desc }
    
(** Translation of equations. *)
and equation ({ eq_desc; eq_write } as eq) =
  match eq_desc with
  | EQeq(p, e) -> 
     { eq with eq_desc = EQeq(p, exp e) }
  | EQpluseq(x, e) -> 
     { eq with eq_desc = EQpluseq(x, exp e) }
  | EQinit(x, e0) ->
     { eq with eq_desc = EQinit(x, exp e0) }
  | EQnext(n, e, e0_opt) -> 
     { eq with eq_desc = EQnext(n, exp e, optional_map exp e0_opt) }
  | EQder(x, e, e0_opt, []) ->
     { eq with eq_desc = EQder(x, exp e, optional_map exp e0_opt, []) }
  | EQmatch(total, e, p_h_list) ->
     let p_h_list = match_handler_block_eq_list eq_write p_h_list in
     { eq with eq_desc = EQmatch(total, exp e, p_h_list) }
  | EQreset(res_eq_list, e) ->
     let res_eq_list = equation_list res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, exp e) }
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list and_eq_list) }
  | EQbefore(before_eq_list) ->
     { eq with eq_desc =
		 EQbefore(equation_list before_eq_list) }
  | EQblock(b) -> { eq with eq_desc = EQblock(block_eq_list b) }
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(x, e) -> Einput(x, exp e)
	 | Eoutput _ -> desc
	 | Eindex(x, e1, e2) ->
	    Eindex(x, exp e1, exp e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, exp e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block_eq_list b_eq_list in
     { eq with eq_desc =
		 EQforall { body with for_index = i_list;
				      for_init = init_list;
				      for_body = b_eq_list } }
  | EQder _ | EQpresent _ | EQautomaton _ | EQemit _ -> assert false
  									  
and equation_list eq_list = List.map equation eq_list
						 
(* Translate a block of equation. [eq_write] is the set of globally *)
(* written variable. The block is completed with missing equations *)
and block_eq_list ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list = locals l_list in
  (* translate the body. *)
  let eq_list = equation_list eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and complete eq_write ({ b_body = eq_list; b_write = eq_write_block } as b) =
  let eq_list, eq_write_block =
    complete_eq_list eq_write eq_write_block eq_list in
  { b with b_body = eq_list; b_write = eq_write_block }
  
and match_handler_exp_list m_h_list =
  List.map (fun ({ m_body = e } as handler) -> 
      { handler with m_body = exp e }) m_h_list    
    
and match_handler_block_eq_list eq_write m_h_list =
  List.map (fun ({ m_zero = zero; m_body = b } as handler) -> 
	    let b = block_eq_list b in
	    let b = if zero then b else complete eq_write b in
	    { handler with m_body = b }) m_h_list    
  
and local ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_eq_list = equation_list l_eq_list in
  { l with l_eq = l_eq_list; l_env = l_env }

and locals l_list =
  match l_list with
  | [] -> []
  | l :: l_list ->
     let l = local l in
     let l_list = locals l_list in
     l :: l_list
  
let implementation impl =
  match impl.desc with
  | Efundecl(n, ({ f_kind = C; f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp e }) }
  | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl _ -> impl
       
let implementation_list impl_list = Misc.iter implementation impl_list
