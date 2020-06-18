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

(* elimation of periods. *)

(* For every function, an extra input [time] is added. Every period *)
(* is translated into the computation of an horizon *)

(* [period(v1(v2))] is translated into *)
(* [local [horizon] h, z *)
(*  do  init h = time + v1 *)
(*  and h = if z then last h + v2 else last h + (time - last time) *)
(*  and z = major && (time >= last h) in *)
(*  z *)

(* [timer(v)] is translated into *)
(* [local [horizon] h, z *)
(*  do init h = time + v *)
(*  and h = if z then infinity else last h + (time - last time) *)
(*  and z = major && (time >= last h) *)
(*  in z] *)

(* An other possible interpretation is to consider that periods and timers *)
(* and taken on absolute time. This is not what is implemented currently. *)
(* The implementation becomes: *)

(* [period(v1(v2))] is translated into: *)
(* [local [horizon] h, cpt, z *)
(*  do cpt = 0 -> if z then pre cpt + 1 else pre cpt *)
(*  and h = cpt * v2 + v1 and z = major && (mod_float time v2 = v1) *)
(*  in z] *)

(* [timer(v)] is translated into: *)
(* [local [horizon] h, z *)
(*  do init h = v and h = if z then infinity else last h *)
(*  and z = major && (time = v) in z] *)

(* finally, it is possible to consider that timers and period are taken on *)
(* absolute time but with a starting date which is local. *)

(* [period(v1(v2))] is translated into: *)
(* local [horizon] h *)
(* do init h = time and z = major && (mod_float (time - last h) v2 = v1) *)
(* and h = if z then time + v2 else last h in z *)

(* A zero-crossing cannot be true twice without time passing *)
(* up(x) =>
    let rec init ztime = -1.0
        and ztime = if z then time else last ztime
        and z = up(if time > last ztime then x else 1.0) in
    z *)
  
open Misc
open Location
open Ident
open Lident
open Initial
open Deftypes
open Zelus
open Zaux


let new_time () = Ident.fresh "time"

(* The main translation function for periods *)
let period major time { p_phase = p1_opt; p_period = p2 } =
  (* let rec [horizon] h = if z then last h + v2 else last h *)
  (*     and init h = time + p1 and z = major && (time >= last h) in z *)
  let horizon = Deftypes.horizon Deftypes.imem in
  let h = Ident.fresh "h" in
  let z = Ident.fresh "z" in
  let p1 = match p1_opt with | None -> Zaux.zero | Some(p1) -> p1 in
  let env =
    Env.add h (Deftypes.entry horizon Initial.typ_float)
	    (Env.add z { t_sort = Deftypes.value;
			 t_typ = Initial.typ_bool } Env.empty) in
  let eq_list = 
    [eq_make h (ifthenelse (bool_var z) (plus (float_last h) p2)
			   (float_last h));
     eq_init h (plus (float_var time) p1);
     eq_make z (and_op major
		       (greater_or_equal (float_var time) (float_last h)))] in
  make_let env eq_list (bool_var z)

(* Ensure that a zero-crossing cannot be done *)
(* twice without time passing *)
let up major time e =
  let z = Ident.fresh "z" in
  let ztime = Ident.fresh "ztime" in
  let env =
    Env.add ztime (Deftypes.entry imemory Initial.typ_float)
	    (Env.add z (Deftypes.entry Sval Initial.typ_float)
		     Env.empty) in
  let eq_list =
    [eq_init ztime minus_one;
     eq_make ztime
	     (ifthenelse (float_var z) (float_var time) (float_last ztime));
     eq_make z
	     (Zaux.up (ifthenelse (greater (float_var time) (float_last ztime))
				e one))] in
  make_let env eq_list (float_var z)

let up major time e = e

(* Add the extra input parameter "time" for hybrid nodes *)
let extra_input time env pat = 
  Env.add time { t_sort = Deftypes.value; t_typ = Initial.typ_float } env,
  Zaux.pairpat (float_varpat time) pat

(** Translation of expressions. *)
let rec expression major time ({ e_desc = e_desc } as e) =
  match e_desc with
  | Eperiod({ p_phase = opt_p1; p_period = p2 }) ->
     period major time
	    { p_phase = Misc.optional_map (expression major time) opt_p1;
	      p_period = expression major time p2 }
  | Eop(Eup, [e_arg]) ->
     { e with e_desc = Eop(Eup, [expression major time e_arg]) }
  | Eop(op, e_list) ->
     { e with e_desc = Eop(op, List.map (expression major time) e_list) }
  | Eapp(app, op, e_list) ->
     (* for hybrid nodes, add the extra input [time] *)
     let op = expression major time op in
     let e_list = List.map (expression major time) e_list in
     let e_list =
       if Types.is_hybrid (List.length e_list - 1) op.e_typ then
         let head, tail = Misc.firsts e_list in
         head @ [Zaux.pair (float_var time) tail]
       else e_list in
     { e with e_desc = Eapp(app, op, e_list) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression major time) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (expression major time) e_list) }
  | Erecord_access(e_record, x) ->
     { e with e_desc = Erecord_access(expression major time e_record, x) }
  | Erecord(l_e_list) ->
     let l_e_list =
       List.map (fun (l, e) -> (l, expression major time e)) l_e_list in
     { e with e_desc = Erecord(l_e_list) }
  | Erecord_with(e_record, l_e_list) ->
     let l_e_list =
       List.map (fun (l, e) -> (l, expression major time e)) l_e_list in
     { e with e_desc = Erecord_with(expression major time e_record, l_e_list) }
  | Etypeconstraint(e, ty) ->
     { e with e_desc = Etypeconstraint(expression major time e, ty) }
  | Elet(l, e) ->
     { e with e_desc = Elet(local major time l, expression major time e) }
  | Eblock(b, e) ->
     { e with e_desc = Eblock(block major time b, expression major time e) }
  | Eseq(e1, e2) ->
     { e with e_desc =
		Eseq(expression major time e1, expression major time e2) }
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e
  | Epresent _ | Ematch _ -> assert false

(* Translation of equations *)
(* [time] is the current time. [eq_list] is a list of equations and *)
(* [env] the current environment *)
and equation major time ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, e) -> { eq with eq_desc = EQeq(p, expression major time e) }
  | EQpluseq(x, e) -> { eq with eq_desc = EQpluseq(x, expression major time e) }
  | EQmatch(total, e, m_h_list) ->
     let m_h_list =
       List.map
         (fun ({ m_body = b } as m_h) ->
	  { m_h with m_body = block major time b })
	 m_h_list in
     { eq with eq_desc = EQmatch(total, expression major time e, m_h_list) }
  | EQreset(res_eq_list, e) ->
     let e = expression major time e in
     let res_eq_list = equation_list major time res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, e) }
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list major time and_eq_list) }
  | EQbefore(before_eq_list) ->
     { eq with eq_desc = EQbefore(equation_list major time before_eq_list) }
  | EQinit(x, e) ->
     { eq with eq_desc = EQinit(x, expression major time e) }
  | EQder(x, e, None, []) -> 
     { eq with eq_desc = EQder(x, expression major time e, None, []) }
  | EQnext(x, e, e_opt) ->
     let e_opt = Misc.optional_map (expression major time) e_opt in
     { eq with eq_desc = EQnext(x, expression major time e, e_opt) }
  | EQblock(b) -> { eq with eq_desc = EQblock(block major time b) }
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
       | Einput(x, e) -> Einput(x, expression major time e)
       | Eoutput _ -> desc
       | Eindex(x, e1, e2) ->
	  Eindex(x, expression major time e1, expression major time e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, expression major time e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block major time b_eq_list in
     { eq with eq_desc = EQforall { body with for_index = i_list;
					      for_init = init_list;
					      for_body = b_eq_list } }
  | EQautomaton _ | EQpresent _ | EQemit _
  | EQder _ -> assert false
		      
and equation_list major time eq_list = List.map (equation major time) eq_list
					  
(** Translate a block *)
and block major time ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list = List.map (local major time) l_list in
  let eq_list = equation_list major time eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and local major time ({ l_eq = eq_list } as l) =
  { l with l_eq = equation_list major time eq_list }

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl(_, { f_kind = (S | AS | A | AD | D | P) }) -> impl
  | Efundecl(n, ({ f_kind = C; f_args = pat_list;
		   f_body = e; f_env = f_env } as body)) ->
     let time = new_time () in
     let f_env, major = Zaux.major f_env in
     let e = expression major time e in
     let head, tail = Misc.firsts pat_list in
     let f_env, tail = extra_input time f_env tail in
     { impl with desc = 
		   Efundecl(n, { body with f_args = head @ [tail]; 
					   f_body = e; f_env = f_env }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list


