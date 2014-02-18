(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
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
(* A period [f1...fn (f'1... f'm)] is translated into sequential circuit *)
(* The next time is computed from the minimum of all internal periods *)

(* The code created by this module assumes that [time] is negative during *)
(* a continuous phase. This ensures that timers are not triggered inside  *)
(* the numerical solver. *)

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

let typ_float = Initial.typ_float

let emake desc ty = 
  { e_desc = desc; e_loc = no_location; e_typ = ty }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty }
let eqmake desc = { eq_desc = desc; eq_loc = no_location }
let varpat x = pmake (Evarpat(x)) typ_float
let boolvarpat x = pmake (Evarpat(x)) Initial.typ_bool
let var x = emake (Elocal(x)) typ_float
let boolvar x = emake (Elocal(x)) Initial.typ_bool
let last x = emake (Elast(x)) typ_float
let elocal env eq_list = 
  { l_eq = eq_list; l_env = env; l_loc = Location.no_location }
let plus e1 e2 = emake (Eapp(Eop(Name("+.")), [e1;e2])) typ_float
let arrow e1 e2 = emake (Eapp(Eminusgreater, [e1;e2])) typ_float
let minop e1 e2 = emake (Eapp(Eop(Name("min")), [e1;e2])) typ_float
let fby e1 e2 = emake (Eapp(Efby, [e1;e2])) typ_float
let greater_or_equal e1 e2 = 
  emake (Eapp(Eop(Modname { qual = "Zlsolve"; id = "time_geq" }),
           [e1;e2])) Initial.typ_bool
let wildpat () = pmake (Ewildpat) typ_float
let pairpat p1 p2 = pmake (Etuplepat[p1;p2]) (Types.product [p1.p_typ; p2.p_typ])
let pair e1 e2 = emake (Etuple[e1;e2]) (Types.product [e1.e_typ; e2.e_typ])
let float f = emake (Econst(Efloat(f))) typ_float
let bool b = emake (Econst(Ebool(b))) Initial.typ_bool
let elet l e = emake (Elet(l, e)) e.e_typ

let new_time () = Ident.fresh "time"
let infinity = emake (Eglobal(Name("infinity"))) typ_float

(** Minimum of two time horizons *)
let min time1 time2 =
  match time1, time2 with
    | None, None -> None
    | None, time2 -> time2
    | time1, None -> time1
    | Some(time1), Some(time2) -> Some(minop time1 time2)

(** Add an extra input and output parameter for hybrid nodes *)
let extra_input time pat_list = (varpat time) :: pat_list

let extra_output next_time e =
  let t =
    match next_time with
      | None -> infinity
      | Some(t) -> t in
  pair e t

let spat_of_zero ({ e_desc = desc; e_loc = loc } as e) = { desc = Econdexp(e); loc = loc }

let block_of_eq n_list n_env eq_list =
  { b_vars = n_list; b_locals = []; b_body = eq_list;
    b_loc = no_location; b_write = Total.empty; b_env = n_env }

let local env eq_list = { l_eq = eq_list; l_env = env; l_loc = no_location }

(** Translation of periods. *)
(** The period [f1...fn (f'1... f'm)] is translated into a set of equations : *)
(** rec present z ->                                                          *)
(**        local y in                                                         *)
(**        do y = f'1 fby ... fby f'm fby y                                    *)
(**        and next_time = (time -> last next_time) +. f1 fby ... fby fn fby y *)
(**        done                                                                *)
(** and init next_time = 0.0                                                  *)
(** and z = (time >= last next_time)                                          *)
(** [next_time] is the next time; the period is true everytime [time = last next_time] *)

let period env eq_list time { p_phase = l1; p_period = l2 } =
  let fby f rest = fby (float f) rest in
  let y = Ident.fresh "p" in
  let z = Ident.fresh "p" in
  let next_time = Ident.fresh "next_t" in
  let env_y = Env.singleton y { t_sort = Val; t_typ = typ_float } in
  let env = 
    Env.add next_time { t_sort = Mem discrete_memory;
                        t_typ = typ_float } 
      (Env.add z { t_sort = Val; t_typ = Initial.typ_bool } env) in
  let p2 = List.fold_right fby l2 (var y) in
  let p1 = List.fold_right fby l1 (var y) in
  let p1 = plus (arrow (var time) (last next_time)) p1 in
  let eq_list =
    (eqmake(EQpresent
	      ([{ p_cond = spat_of_zero (boolvar z); 
                  p_env = Env.empty; 
                  p_body = 
		  block_of_eq [y] env_y [eqmake(EQeq(varpat y, p2)); 
					 eqmake(EQeq(varpat next_time, p1))] }],
               None))) ::
      (eqmake(EQinit(varpat next_time, float 0.0, None))) :: 
      (eqmake(EQeq(boolvarpat z, greater_or_equal (var time) (last next_time)))) ::
      eq_list in
  arrow (bool (List.hd (l1 @ l2) = 0.0)) (boolvar z),
  var next_time,
  eq_list, env

(** Add an equation [o = e] to a block if a next periodic time is *)
(** computed by [e]. Adds [o = time] otherwise *)
let add_to_block o next_time ( { b_body = eq_list } as b) =
  let e = match next_time with | None -> infinity | Some(e) -> e in
  { b with b_body = (eqmake (EQeq(varpat o, e))) :: eq_list }
  
let is_compiled_with_period f = Global.period_desc (Modules.find_value f)
  
(** Translation of expressions. *)
(* [nexpression time next_time env e = e', ok] takes a global input [time] *)
(* the expression computing the next horizon for the context and an *)
(* an expression [e]. It returns a new expression [e'] and a boolean [ok] *)
(* [ok = true] if [e'] have generated a period *)
(* expressions must be in normal form before the transformation applies *)
let rec nexpression time e =
  let rec exprec next_time ({ e_desc = desc } as e) =
    match desc with
      | Elet(l, let_e) ->
          let l, next_time_l = local time l in
          let let_e = exprec (min next_time_l next_time) let_e in
          { e with e_desc = Elet(l, let_e) }
      | _ -> extra_output next_time e in
  exprec None e

(* [equation time (eq_list, next_time, env) eq = eq', (eq_list', next_time', env']*)
(* translated equation [eq' :: eq_list], the next horizon [next_time'] and an *)
(* extended environment [env'] *)
and equation time (eq_list, next_time, env) ({ eq_desc = desc } as eq) =
  match desc with 
    | EQeq(pat, { e_desc = Eperiod p }) -> 
        let e, next_time_for_period, eq_list, env = period env eq_list time p in
        { eq with eq_desc = EQeq(pat, e) } :: eq_list,
        min next_time (Some next_time_for_period), env
    | EQeq(p, ({ e_desc = Eapp(Eop(f), e_list) } as e)) 
        when Types.is_a_hybrid_node f && is_compiled_with_period f ->
        let o = new_time () in
        let eq =
          { eq with eq_desc =
              EQeq(pairpat p (varpat o),
                  { e with e_desc = Eapp(Eop(f), var time :: e_list) }) } in
        eq :: eq_list,
        min next_time (Some (var o)),
        Env.add o { t_sort = Val; t_typ = typ_float } env
    | EQmatch(total, e, p_h_list) ->
        (* a fresh name for the result of the horizon in each branch *)
        let o = new_time () in
        let p_h_next_time_list =
          List.map 
            (fun ({ m_body = b } as p_h) -> 
              let b, next_time_b = block time b in 
	      { p_h with m_body = b }, next_time_b)
          p_h_list in
        (* is-there a period in one branch? *)
        let at_least_one_period =
          List.exists 
	    (fun (_, next) -> match next with | None -> false | Some _ -> true) 
            p_h_next_time_list in
        let p_h_list, next_time, env =
          if at_least_one_period
          then 
            (* add an equation [o = next_time_b] in every branch for which *)
            (* [next_time_b] is not None. [o = infinity] otherwise *)
            List.map 
              (fun ({ m_body = b } as p_h, next_time_b) -> 
                { p_h with m_body = add_to_block o next_time_b b }) 
              p_h_next_time_list,
            min (Some(var o)) next_time,
            Env.add o { t_sort = Val; t_typ = typ_float } env
          else
            List.map (fun (p_h, _) -> p_h) p_h_next_time_list, next_time, env in
         { eq with eq_desc = EQmatch(total, e, p_h_list) } :: eq_list,
         next_time, env
    | EQreset(b, e) -> 
        let b, next_time_b = block time b in
        let b, next_time, env =
          match next_time_b with
            | None -> b, next_time, env
            | Some(e) -> 
                (* add an extra equation [o = e] *)
                let o = new_time () in
                { b with b_body = (eqmake(EQeq(varpat o, e))) :: b.b_body },
                min (Some(var o)) next_time,
                Env.add o { t_sort = Val; t_typ = typ_float } env in
        { eq with eq_desc = EQreset(b, e) } :: eq_list,
        next_time, env
    | EQpresent(p_h_list, b_opt) ->
        let next_time, b_opt =
          match b_opt with 
            | None -> next_time, None 
            | Some(b) -> let b, next_time_b = block time b in
                         min next_time_b next_time, Some(b) in
        { eq with eq_desc = EQpresent(p_h_list, b_opt) } :: eq_list, 
        next_time, env
    | EQemit(x, e_opt) ->
        { eq with eq_desc = EQemit(x, e_opt) } :: eq_list, 
        next_time, env
    | EQeq _ | EQinit _ | EQnext _ | EQder _ -> eq :: eq_list, next_time, env
    | EQautomaton _ -> assert false

and equation_list time next_time eq_list =
  List.fold_left (equation time) ([], next_time, Env.empty) eq_list      

(** Translate a block *)
and block time ({ b_vars = n_list; b_body = eq_list; b_env = n_env } as b) =
  (* add local declarations [local x1 in ... in local xn in ...] *)
  let add_locals env n_list n_env =
    let add x entry (n_list, n_env) = x :: n_list, Env.add x entry n_env in
    Env.fold add env (n_list, n_env) in
  
  let eq_list, next_time, env = equation_list time None eq_list in
  let n_list, n_env = add_locals env n_list n_env in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }, next_time

and local time ({ l_eq = eq_list } as l) =
  let eq_list, next_time_eq, env = equation_list time None eq_list in
  { l with l_eq = eq_list; l_env = Env.append env l.l_env },
  next_time_eq

let set_period_flag f =
  Global.set_period_desc (Modules.find_value (Lident.Name(f))) (Some true)

let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _  
      | Efundecl(_, { f_kind = (A | AD | D) }) -> impl
      | Efundecl(n, ({ f_kind = C; f_args = pat_list; f_body = e } as body)) ->
          let time = new_time () in
          let e = nexpression time e in
          let pat_list = extra_input time pat_list in
          set_period_flag n;
          { impl with desc = 
              Efundecl(n, { body with f_kind = C; f_args = pat_list; f_body = e }) }

let implementation_list impl_list = Misc.iter implementation impl_list

