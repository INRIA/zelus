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

(* Elimation of disc. This construction may be removed *)

(* [disc(e)] is translated into [false -> major on (e <> last e)] *)

open Misc
open Location
open Ident
open Lident
open Initial
open Deftypes
open Zelus
open Zaux

(* [disc(x)] is translated into [let x = e in major on (x <> (x fby x)] *)

let disc major e =
  let on_op z e = Zaux.and_op z e in
  if Unsafe.exp e
  then (* disc(e)] = [let x = e in major on (x <> (x fby x))] *)
    let x = Ident.fresh "x" in
    let env = Env.singleton x { t_sort = Deftypes.value;
				t_typ = e.e_typ } in
    let xv = var x e.e_typ in
    make_let env [eq_make x e] (on_op major (diff xv (fby xv xv)))
  else on_op major (diff e (fby e e))
    
(** Translation of expressions. *)
let rec expression major ({ e_desc = e_desc } as e) =
  match e_desc with
  | Eop(Edisc, [e]) -> disc major (expression major e)
  | Eop(op, e_list) ->
     { e with e_desc = Eop(op, List.map (expression major) e_list) }
  | Eapp(app, op, e_list) ->
     let op = expression major op in
     let e_list = List.map (expression major) e_list in
     { e with e_desc = Eapp(app, op, e_list) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression major) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (expression major) e_list) }
  | Erecord_access(e_record, x) ->
     { e with e_desc = Erecord_access(expression major e_record, x) }
  | Erecord(l_e_list) ->
     let l_e_list = List.map (fun (l, e) -> (l, expression major e)) l_e_list in
     { e with e_desc = Erecord(l_e_list) }
  | Erecord_with(e_record, l_e_list) ->
     let l_e_list = List.map (fun (l, e) -> (l, expression major e)) l_e_list in
     { e with e_desc = Erecord_with(expression major e_record, l_e_list) }
  | Etypeconstraint(e, ty) ->
     { e with e_desc = Etypeconstraint(expression major e, ty) }
  | Elet(l, e) ->
     { e with e_desc = Elet(local major l, expression major e) }
  | Eblock(b, e) ->
     { e with e_desc = Eblock(block major b, expression major e) }
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(expression major e1, expression major e2) }
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e
  | Epresent _ | Ematch _ | Eperiod _ -> assert false

(* Translation of equations *)
(* [major] is the current major. [eq_list] is a list of equations and *)
(* [env] the current environment *)
and equation major ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, e) -> { eq with eq_desc = EQeq(p, expression major e) }
  | EQpluseq(x, e) -> { eq with eq_desc = EQpluseq(x, expression major e) }
  | EQmatch(total, e, m_h_list) ->
     let m_h_list =
       List.map
         (fun ({ m_body = b } as m_h) -> { m_h with m_body = block major b })
	 m_h_list in
     { eq with eq_desc = EQmatch(total, expression major e, m_h_list) }
  | EQreset(res_eq_list, e) ->
     let e = expression major e in
     let res_eq_list = equation_list major res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, e) }
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list major and_eq_list) }
  | EQbefore(before_eq_list) ->
     { eq with eq_desc = EQbefore(equation_list major before_eq_list) }
  | EQinit(x, e) ->
     { eq with eq_desc = EQinit(x, expression major e) }
  | EQder(x, e, None, []) -> 
     { eq with eq_desc = EQder(x, expression major e, None, []) }
  | EQnext(x, e, e_opt) ->
     let e_opt = Misc.optional_map (expression major) e_opt in
     { eq with eq_desc = EQnext(x, expression major e, e_opt) }
  | EQblock(b) -> { eq with eq_desc = EQblock(block major b) }
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
       | Einput(x, e) -> Einput(x, expression major e)
       | Eoutput _ -> desc
       | Eindex(x, e1, e2) ->
	  Eindex(x, expression major e1, expression major e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, expression major e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block major b_eq_list in
     { eq with eq_desc = EQforall { body with for_index = i_list;
					      for_init = init_list;
					      for_body = b_eq_list } }
  | EQautomaton _ | EQpresent _ | EQemit _
  | EQder _ -> assert false
		      
and equation_list major eq_list = List.map (equation major) eq_list
					  
(** Translate a block *)
and block major ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list = List.map (local major) l_list in
  let eq_list = equation_list major eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and local major ({ l_eq = eq_list } as l) =
  { l with l_eq = equation_list major eq_list }

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl(_, { f_kind = (S | AS | A | AD | D | P) }) -> impl
  | Efundecl(n, ({ f_kind = C; f_body = e; f_env = f_env } as body)) ->
     let f_env, major = Zaux.major f_env in
     let e = expression major e in
     { impl with desc = 
		   Efundecl(n, { body with f_body = e; f_env = f_env }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
  
