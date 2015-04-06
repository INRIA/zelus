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
(* elimation of periods. An extra input [time] is added and an *)
(* extra output [nexttime] is added *)
(* A period [f1 (f'1)] is translated into discrete code *)
(* The next time is computed from the minimum of all internal periods *)

(* A cascade of transitions is stopped when the next horizon is strictly *)
(* greater than the current one. When an equation [x = e] *)
(* on a shared variable [x] appears inside a present handler, *)
(* an extra step is added. This is done by setting *)
(* [nexttime = time]. Otherwise, [nexttime = infinity] *)

(* The translation takes the current time [time] and it returns              *)
(* a set of equations defining local periods and an extra output [next_time] *)
(* programs must be normalized first with every stateful function application *)
(* appearing in equations, i.e., [p = f(e1,...,en)] as well as periods *)
(* p = period ...(...) *)
(* e ::= op(e,...,e) | let E in e | .. with E stateless *)
(* df ::= e | let E in df *)
(* eq ::= p = df | p = df every c | ... | ... *)

open Misc
open Location
open Ident
open Lident
open Initial
open Deftypes
open Zelus

let emake desc ty = 
  { e_desc = desc; e_loc = no_location; e_typ = ty; e_caus = [] }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty; p_caus = [] }
let eqmake desc =
  { eq_desc = desc; eq_loc = no_location; eq_before = S.empty;
    eq_after = S.empty; eq_write = Deftypes.empty }
let varpat id ty = pmake (Evarpat(id)) ty
let var id ty = emake (Elocal(id)) ty
let float_varpat x = varpat x Initial.typ_float
let truepat = pmake (Econstpat(Ebool(true))) Initial.typ_bool
let bool_varpat x = varpat x Initial.typ_bool
let float_var x = var x Initial.typ_float
let bool_var x = var x Initial.typ_bool
let elocal env eq_list = 
  { l_eq = eq_list; l_env = env; l_loc = Location.no_location }
let plus e1 e2 = emake (Eapp(Eop(false, Modname(Initial.pervasives_name "+.")),
				 [e1;e2])) Initial.typ_float
let minus e1 e2 = emake (Eapp(Eop(false, Modname(Initial.pervasives_name "-.")),
				 [e1;e2])) Initial.typ_float
let float_last x = emake (Elast(x)) Initial.typ_float
let bool_last x = emake (Elast(x)) Initial.typ_bool
let ifthenelse e1 e2 e3 = emake (Eapp(Eifthenelse, [e1;e2;e3])) e2.e_typ
let minop e1 e2 = emake (Eapp(Eop(false, Modname(Initial.pervasives_name "min")),
			      [e1;e2])) Initial.typ_float
let greater_or_equal e1 e2 = 
  emake (Eapp(Eop(false, Modname(Initial.pervasives_name ">=")), [e1;e2])) 
    Initial.typ_bool
let wildpat () = pmake (Ewildpat) typ_float
let pairpat p1 p2 = pmake (Etuplepat[p1;p2]) (Types.product [p1.p_typ; p2.p_typ])
let pair e1 e2 = emake (Etuple[e1;e2]) (Types.product [e1.e_typ; e2.e_typ])
let float f = emake (Econst(Efloat(f))) Initial.typ_float
let bool b = emake (Econst(Ebool(b))) Initial.typ_bool
let elet l e = emake (Elet(l, e)) e.e_typ

let new_time () = Ident.fresh "time"
let infinity = 
  emake (Eglobal(Modname(Initial.pervasives_name "infinity"))) typ_float

(** Minimum of two time horizons *)
let min time1 time2 =
  match time1, time2 with
    | None, None -> None
    | None, time2 -> time2
    | time1, None -> time1
    | Some(time1), Some(time2) -> Some(minop time1 time2)

(** Add an extra input and output parameter for hybrid nodes *)
let extra_input time env pat_list = 
  Env.add time { t_sort = Val; t_typ = Initial.typ_float } env,
  (float_varpat time) :: pat_list

let extra_output next_time e =
  let t =
    match next_time with
      | None -> infinity
      | Some(t) -> t in
  pair e t

let spat_of_zero 
      ({ e_desc = desc; e_loc = loc } as e) = { desc = Econdexp(e); loc = loc }

let block_of_eq n_list n_env eq_list =
  { b_vars = n_list; b_locals = []; b_body = eq_list;
    b_loc = no_location; b_write = Total.empty; b_env = n_env }

(** Translation of periods. *)
(* The periods (p2) and p1(p2) are translated into a set of equations *)

(* [rec init horizon = p0 
    and horizon = last horizon + (if change then p2 else 0)
    and change = time >= last horizon and init change = z0
    and z = change] *)
(* where p0 = match p1 with None -> p2 | Some(v1) -> v1 *)
(* and z0 = match p1 with None -> true | Some _ -> false *)
let period next_env eq_list time z { p_phase = p1_opt; p_period = p2 } =
  let horizon = Ident.fresh "horizon" in
  let change = Ident.fresh "change" in
  let next_env = 
    Env.add horizon { t_sort = Mem discrete_memory; t_typ = typ_float } 
	    (Env.add change { t_sort = Mem discrete_memory; t_typ = typ_bool } 
		     next_env) in
  let p0, z0 = 
    match p1_opt with | None -> p2, true | Some(p1) -> p1, false in
  let eq_list = 
    (eqmake(EQinit(horizon, float p0)))
    :: (eqmake(EQeq(float_varpat horizon, 
		    (plus (float_last horizon)
			  (ifthenelse (bool_var change) (float p2) 
				      (float 0.0))))))
    :: (eqmake(EQeq(bool_varpat change, 
		    greater_or_equal (float_var time) (float_last horizon))))
    :: (eqmake(EQeq(bool_varpat z, bool_var change)))
    :: (eqmake(EQinit(change, bool z0))) :: eq_list in
  float_var horizon, eq_list, next_env

(* [rec init horizon = p1 + time 
    and horizon = if change then p2 + time 
                  else last horizon + (time - last ltime)
    and ltime = if time >= 0.0 then time else last ltime and init ltime = time
    and change = time >= last horizon
    and z = change] *)
let period2 next_env eq_list time z { p_phase = p1_opt; p_period = p2 } =
  let horizon = Ident.fresh "horizon" in
  let change = Ident.fresh "change" in
  let ltime = Ident.fresh "ltime" in
  let next_env = 
    Env.add horizon { t_sort = Mem discrete_memory; t_typ = typ_float } 
	    (Env.add ltime { t_sort = Mem discrete_memory; t_typ = typ_float } 
		     (Env.add change { t_sort = Mem discrete_memory; t_typ = typ_bool } next_env)) in
  let p1 = 
    match p1_opt with | None -> 0.0 | Some(p1) -> p1 in
  let eq_list = 
    (eqmake(EQinit(horizon, plus (float p1) (float_var time))))
    :: (eqmake(EQeq(float_varpat horizon, 
		    ifthenelse (bool_var change)
			       (plus (float p2) (float_var time))
			       (plus (float_last horizon) (minus (float_var time) (float_last ltime))))))
    :: (eqmake(EQinit(ltime,
		      ifthenelse (greater_or_equal (float_var time) (float 0.0)) (float_var time) (float_last ltime))))
    :: (eqmake(EQeq(float_varpat ltime, float_var time)))
    :: (eqmake(EQeq(bool_varpat change, 
		    greater_or_equal (float_var time) (float_last horizon))))
    :: (eqmake (EQeq(bool_varpat z, bool_var change))):: eq_list in
  float_var horizon, eq_list, next_env

(* Translation of discrete zero-crossings into synchronous code *)
let disc next_env eq_list o e =
  (* o = disc(e)] = [o = false fby (e <> pre(e))] = *)
  (*              = [p = e and o = false -> e <> last p]  *)
  let p = Ident.fresh "p" in
  let next_env =
    Env.add p { t_sort = Mem { discrete_memory with t_initialized = false }; 
		t_typ = e.e_typ } next_env in
  next_env,
  eqmake (EQeq(varpat p e.e_typ, e)) ::
    eqmake (EQeq(o, 
		 emake (Eapp(Eminusgreater,
			    [emake (Econst(Ebool(false))) Initial.typ_bool;
			     emake (Eapp(Eop(false, 
					    Modname(Initial.pervasives_name "<>")),
					[e; emake (Elast(p)) e.e_typ])) Initial.typ_bool]
		 )) Initial.typ_bool)) :: eq_list
 
(** Add an equation [o = e] to a block if a next periodic time is *)
(** computed by [e]. *)
let add_to_block o next_time ( { b_body = eq_list } as b) =
  let eq_list = 
    match next_time with 
      | None -> eq_list 
      | Some(e) -> (eqmake (EQeq(float_varpat o, e))) :: eq_list in
  { b with b_body = eq_list }
    
(** Translation of expressions. *)
(* [nexpression env time next_time e = e', ok] takes a global input [time] *)
(* the expression computing the next horizon for the context and an *)
(* an expression [e]. It returns a new expression [e'] and a boolean [ok] *)
(* [ok = true] if [e'] have generated a period *)
(* expressions must be in normal form before the transformation applies *)
let rec nexpression env time e =
  let rec exprec next_time ({ e_desc = desc } as e) =
    match desc with
      | Elet(l, let_e) ->
          let l, next_time_l = local env time l in
          let let_e = exprec (min next_time_l next_time) let_e in
          { e with e_desc = Elet(l, let_e) }
      | _ -> extra_output next_time e in
  exprec None e

(* [equation env time (eq_list, next_time, next_env) eq =          *)
(*                              eq', (eq_list', next_time', env']  *)
(* translated equation [eq' :: eq_list], the next horizon [next_time'] and an *)
(* extended environment [next_env] *)
and equation env time (eq_list, next_time, next_env) ({ eq_desc = desc } as eq) =
  match desc with 
    (* translation of periods *)
    | EQeq({ p_desc = Evarpat(z) }, { e_desc = Eperiod pe }) -> 
        let horizon, eq_list, next_env = 
	  period next_env eq_list time z pe in
        eq_list, min next_time (Some horizon), next_env
    (* translation of a discrete zero-crossing *)
    | EQeq(o, { e_desc = Eapp(Edisc, [e]) }) ->
        let next_env, eq_list = disc next_env eq_list o e in
	eq_list, next_time, next_env
    | EQeq(p, ({ e_desc = Eapp(Eop(is_inline, f), e_list) } as e)) 
        when Types.is_a_hybrid_node f ->
        let o = new_time () in
        let eq =
          { eq with eq_desc =
              EQeq(pairpat p (float_varpat o),
                  { e with e_desc = Eapp(Eop(is_inline, f), 
					 float_var time :: e_list) }) } in
        eq :: eq_list,
        min next_time (Some (float_var o)),
        Env.add o { t_sort = Val; t_typ = typ_float } next_env
    | EQmatch(total, e, m_h_list) ->
        (* a fresh name for the result of the horizon in each branch *)
        let o = new_time () in
        let m_h_next_time_list =
          List.map 
            (fun ({ m_body = b; m_zero = zero; m_env = l_env } as p_h) -> 
              let b, next_time_b = block (Env.append l_env env) zero time b in 
	      { p_h with m_body = b }, next_time_b)
          m_h_list in
        (* is-there a period in one branch? *)
        let at_least_one_period =
          List.exists 
	    (fun (_, next) -> match next with | None -> false | Some _ -> true) 
            m_h_next_time_list in
        let m_h_list, next_time, next_env =
          if at_least_one_period
          then 
            (* add an equation [o = next_time_b] in every branch for which *)
            (* [next_time_b] is not None. The default value is infinity *)
            List.map 
              (fun ({ m_body = b } as m_h, next_time_b) -> 
                { m_h with m_body = add_to_block o next_time_b b }) 
              m_h_next_time_list,
            min (Some(float_var o)) next_time,
            Env.add o 
	      { t_sort = 
		  ValDefault (Cglobal 
				(Modname(Initial.pervasives_name "infinity"))); 
		t_typ = typ_float } next_env
          else
            List.map 
	      (fun (m_h, _) -> m_h) m_h_next_time_list, next_time, next_env in
         { eq with eq_desc = EQmatch(total, e, m_h_list) } :: eq_list,
         next_time, next_env
    | EQreset(res_eq_list, e) -> 
        let res_eq_list, next_time, next_env =
          equation_list env time next_time next_env res_eq_list in
	{ eq with eq_desc = EQreset(res_eq_list, e) } :: eq_list,
        next_time, next_env
    | EQeq _ | EQset _ | EQinit _ | EQnext _ | EQder _ -> 
        eq :: eq_list, next_time, next_env
    | EQautomaton _ | EQpresent _ | EQemit _ | EQblock _ -> assert false

and equation_list env time next_time next_env eq_list =
  List.fold_left (equation env time) ([], next_time, next_env) eq_list      

(* does the block contains an equation [next x = e] on a shared variable? *)
and next env { b_write = { dv = v} } =
  let next x =
    let { t_sort = sort } = Env.find x env in
    match sort with
      | Mem { t_last_is_used = is_last } -> is_last
      | _ -> false in
  S.exists next v

(** Translate a block *)
(* [zero = true] means that the block is activated on a zero-crossing instant. *)
(* [time] is the current time. The translation returns a new block and *)
(* an optional expression that contain the next computed horizon. *)
and block env zero time 
    ({ b_vars = n_list; b_body = eq_list; b_env = n_env } as b) =
  (* add local declarations [local x1 in ... in local xn in ...] *)
  let add_locals env n_list n_env =
    let add x entry (n_list, n_env) = x :: n_list, Env.add x entry n_env in
    Env.fold add env (n_list, n_env) in
  
  let eq_list, next_time, next_env = 
    equation_list (Env.append n_env env) time None Env.empty eq_list in

  (* compute the next horizon *)
  let next_time =
    if zero then
      (* if the block is activated on a zero-crossing instant *)
      (* a new step must be performed in case the block contains *)
      (* an equation [x = ...] on a shared memory variable [x] *)
      let at_least_one_next = next env b in
      if at_least_one_next then
       (* the new minimum is [time] *) (Some (float_var time))
      else (* otherwise it is [next_time] *) next_time
    else next_time in
  let n_list, n_env = add_locals next_env n_list n_env in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }, next_time

and local env time ({ l_eq = eq_list; l_env = l_env } as l) =
  let env = Env.append l_env env in
  let eq_list, next_time_eq, next_env = 
    equation_list env time None Env.empty eq_list in
  { l with l_eq = eq_list; l_env = Env.append next_env l_env },
  next_time_eq

let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _  
      | Efundecl(_, { f_kind = (A | AD | D) }) -> impl
      | Efundecl(n, ({ f_kind = C; f_args = pat_list; 
		       f_body = e; f_env = f_env } as body)) ->
          let time = new_time () in
          let e = nexpression f_env time e in
          let f_env, pat_list = extra_input time f_env pat_list in
          { impl with desc = 
			Efundecl(n, { body with f_kind = C; f_args = pat_list; 
						f_body = e; f_env = f_env }) }

let implementation_list impl_list = Misc.iter implementation impl_list
