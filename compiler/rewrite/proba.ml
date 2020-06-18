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

(* translation of a probabilistic node into a node. *)
(* the translation is applied to normalised programs *)

(* every probabilistic node:
   
   [let proba f x1 ... xn = ...]

is translated into:

   [let node f x1 ... prob xn = ...]

and every application of a probabilistic node:

   [f e1 ... en]

into:

   [f e1 ... prob en]
 *)

open Zelus
open Deftypes
open Lident
open Ident
       
let new_prob () = Ident.fresh "prob"

(* If the extra parameter [prob] is given a type, say [prob] *)
(* this type but be bind to an actual module or interface. This makes *)
(* the translation dependent on the infer function. This is why we *)
(* chose to give it a type variable. *)
let typ_prob = Types.make (Deftypes.Tvar)
let prob_varpat x = Zaux.varpat x typ_prob
let prob_var x = Zaux.var x typ_prob
							  
(* Add the extra input parameter "time" for hybrid nodes *)
let extra_input prob env = 
  Env.add prob { t_sort = Deftypes.value; t_typ = typ_prob } env,
  (prob_varpat prob)

(** Translation of expressions. *)
let rec expression prob ({ e_desc = e_desc } as e) =
  match e_desc with
  | Eperiod({ p_phase = opt_p1; p_period = p2 }) ->
     { e with e_desc =
		Eperiod({ p_phase =
			    Misc.optional_map (expression prob) opt_p1;
			  p_period = expression prob p2 }) }
  | Eop(op, e_list) ->
     { e with e_desc = Eop(op, List.map (expression prob) e_list) }
  | Eapp(app, op, e_list) ->
     let op = expression prob op in
     let e_list = List.map (expression prob) e_list in
     let e_list =
       if Types.is_probabilistic (List.length e_list - 1) op.e_typ then
         let head, tail = Misc.firsts e_list in
         head @ [Zaux.pair (prob_var prob) tail]
       else e_list in
     { e with e_desc = Eapp(app, op, e_list) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression prob) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (expression prob) e_list) }
  | Erecord_access(e_record, x) ->
     { e with e_desc = Erecord_access(expression prob e_record, x) }
  | Erecord(l_e_list) ->
     let l_e_list =
       List.map (fun (l, e) -> (l, expression prob e)) l_e_list in
     { e with e_desc = Erecord(l_e_list) }
  | Erecord_with(e_record, l_e_list) ->
     let l_e_list =
       List.map (fun (l, e) -> (l, expression prob e)) l_e_list in
     { e with e_desc = Erecord_with(expression prob e_record, l_e_list) }
  | Etypeconstraint(e, ty) ->
     { e with e_desc = Etypeconstraint(expression prob e, ty) }
  | Elet(l, e) ->
     { e with e_desc = Elet(local prob l, expression prob e) }
  | Eblock(b, e) ->
     { e with e_desc = Eblock(block prob b, expression prob e) }
  | Eseq(e1, e2) ->
     { e with e_desc =
		Eseq(expression prob e1, expression prob e2) }
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e
  | Epresent _ | Ematch _ -> assert false

(* Translation of equations *)
and equation prob ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, e) -> { eq with eq_desc = EQeq(p, expression prob e) }
  | EQpluseq(x, e) -> { eq with eq_desc = EQpluseq(x, expression prob e) }
  | EQmatch(total, e, m_h_list) ->
     let m_h_list =
       List.map
         (fun ({ m_body = b } as m_h) ->
	  { m_h with m_body = block prob b })
	 m_h_list in
     { eq with eq_desc = EQmatch(total, expression prob e, m_h_list) }
  | EQreset(res_eq_list, e) ->
     let e = expression prob e in
     let res_eq_list = equation_list prob res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, e) }
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list prob and_eq_list) }
  | EQbefore(before_eq_list) ->
     { eq with eq_desc = EQbefore(equation_list prob before_eq_list) }
  | EQinit(x, e) ->
     { eq with eq_desc = EQinit(x, expression prob e) }
  | EQder(x, e, None, []) -> 
     { eq with eq_desc = EQder(x, expression prob e, None, []) }
  | EQnext(x, e, e_opt) ->
     let e_opt = Misc.optional_map (expression prob) e_opt in
     { eq with eq_desc = EQnext(x, expression prob e, e_opt) }
  | EQblock(b) -> { eq with eq_desc = EQblock(block prob b) }
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
       | Einput(x, e) -> Einput(x, expression prob e)
       | Eoutput _ -> desc
       | Eindex(x, e1, e2) ->
	  Eindex(x, expression prob e1, expression prob e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, expression prob e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block prob b_eq_list in
     { eq with eq_desc = EQforall { body with for_index = i_list;
					      for_init = init_list;
					      for_body = b_eq_list } }
  | EQautomaton _ | EQpresent _ | EQemit _
  | EQder _ -> assert false
		      
and equation_list prob eq_list = List.map (equation prob) eq_list
					  
(** Translate a block *)
and block prob ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list = List.map (local prob) l_list in
  let eq_list = equation_list prob eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and local prob ({ l_eq = eq_list } as l) =
  { l with l_eq = equation_list prob eq_list }

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl(_, { f_kind = (S | AS | A | AD | D | C) }) -> impl
  | Efundecl(n, ({ f_kind = P; f_args = pat_list;
		   f_body = e; f_env = f_env } as body)) ->
     let prob = new_prob () in
     let e = expression prob e in
     let head, tail = Misc.firsts pat_list in
     let f_env, prob = extra_input prob f_env in
     { impl with desc = 
		   Efundecl(n,
			    { body with f_kind = D;
					f_args =
					  head @ [Zaux.pairpat prob tail]; 
					f_body = e; f_env = f_env }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
