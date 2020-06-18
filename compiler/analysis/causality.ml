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

(* causality check *)

(* C | H |-cfree e: ct *)
(* [C] is a constraint and [H] is an environment *)

(* There are two kind of types. c is a causality tag (or time stamp). *)
(* ct is a type whose leaves are causality tags. *)
(* causality tags are associated to a strict partial order. *)
(* The relation c1 < c2 with |-cfree e1: c1 and |-cfree e2: c2 *)
(* means that e1 must be computed strictly before c2 *)
(* The causality analysis is able to express that a block executes atomically, *)
(* that is, it is considered as iff all output would depend on all input *)
(* For that purpose, cfree is a causality tag greater than that of all the *)
(* free variables in e *)

open Misc
open Ident
open Global
open Zelus
open Location
open Deftypes
open Defcaus
open Pcaus
open Causal

let print x = Misc.internal_error "unbound" Printer.name x

(* Main error message *)
type error =
    { kind: kind;
      cycle: cycle;
      env: Causal.tentry Env.t }
	       
 and kind =
   | Cless_than of tc * tc
   | Cless_than_name of Ident.t * tc * tc

(* dependence cycle and the current typing environment *)
exception Error of location * error

let error loc kind = raise (Error(loc, kind))

(* let message loc kind =
  begin
    match kind with
    | Cless_than(left_tc, right_tc, env, cycle) ->
        let env, cset, rel, left_tc, right_tc =
          Causal.simplify_by_io_env env left_tc right_tc in
        let cycle = Causal.shrink_cycle cset cycle in
        Format.eprintf
          "@[%aCausality error: This expression has causality type@ %a,@ \
           whereas it should be less than@ %a@.\
           Here is an example of a cycle:@.%a@.\
           in the current typing environment:@.%a%a@.@]"
          output_location loc
          Pcaus.ptype left_tc
          Pcaus.ptype right_tc
          (Pcaus.cycle false) cycle
          Causal.penv env
          Causal.prel rel
  end;
  raise Misc.Error *)

let message loc { kind; cycle } =
  begin
    match kind with
    | Cless_than(left_tc, right_tc) ->
        let c_set = vars (vars S.empty left_tc) right_tc in
        let cycle = Causal.keep_names_in_cycle c_set cycle in
        Format.eprintf
          "@[%aCausality error: This expression has causality type@ %a,\
           @ whereas it should be less than@ %a@.\
           Here is an example of a cycle:@.%a@.@]"
          output_location loc
          Pcaus.ptype left_tc
          Pcaus.ptype right_tc
          (Pcaus.cycle true) cycle
    | Cless_than_name(name, left_tc, right_tc) ->
        let c_set = vars (vars S.empty left_tc) right_tc in
        let cycle = Causal.keep_names_in_cycle c_set cycle in
        Format.eprintf
          "@[%aCausality error: The variable %s has causality type@ %a,\
           @ whereas it should be less than@ %a@.\
           Here is an example of a cycle:@.%a@.@]"
          output_location loc
          (Ident.source name)
	  Pcaus.ptype left_tc
          Pcaus.ptype right_tc
          (Pcaus.cycle true) cycle
  end;
  raise Misc.Error

let less_than loc env actual_tc expected_tc =
  try
    Causal.less actual_tc expected_tc
  with
  | Causal.Clash(cycle) ->
     error loc
	   { kind = Cless_than(actual_tc, expected_tc); env = env; cycle = cycle }

let less_than_name loc env name actual_tc expected_tc =
  try
    Causal.less actual_tc expected_tc
  with
  | Causal.Clash(cycle) ->
     error loc
	   { kind = Cless_than_name(name, actual_tc, expected_tc);
	     env = env; cycle = cycle }

let less_than_c loc env actual_c expected_c =
  try
    Causal.less_c actual_c expected_c
  with
  | Causal.Clash(cycle) ->
     error loc
	   { kind = Cless_than(atom actual_c, atom expected_c);
	     env = env; cycle = cycle }

(** Typing a pattern. [pattern env p = tc] where [tc] is the type *)
(* of pattern [p] in [env] *)
let pattern env pat =
  (* check that the type of pat is less than a type synchronised on [c] *)
  let rec pattern_less_than_on_c pat c =
    let actual_tc = pattern pat in
    let expected_tc = Causal.skeleton_on_c c pat.p_typ in
    (* the order [expected_tc < actual_tc] is mandatory, *)
    (* not the converse *)
    less_than pat.p_loc env expected_tc actual_tc

  and pattern ({ p_desc = desc; p_loc = loc; p_typ = ty } as pat) =
    let tc = match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ ->
        Causal.skeleton_on_c (Causal.new_var ()) ty
    | Evarpat(x) ->
       let { t_typ = actual_tc } =
         try Env.find x env with | Not_found -> print x in
       (* every variable that is not a function has an atomic type *)
       let expected_tc = Causal.skeleton_for_variables pat.p_typ in
       less_than loc env expected_tc actual_tc;
       expected_tc
    | Econstr1pat(_, pat_list) ->
        let c = Causal.new_var () in
        List.iter (fun pat -> pattern_less_than_on_c pat c) pat_list;
        Causal.skeleton_on_c c ty
    | Etuplepat(pat_list) ->
        product(List.map pattern pat_list)
    | Erecordpat(l) ->
       (* from the causality point of view, a record is considered to be *)
       (* atomic *)
       let c = Causal.new_var () in
       List.iter (fun (_, p) -> pattern_less_than_on_c p c) l;
       Causal.skeleton_on_c c ty
    | Etypeconstraintpat(p, _) -> pattern p
    | Eorpat(p1, p2) ->
        let tc1 = pattern p1 in
        let tc2 = pattern p2 in
        Causal.suptype true tc1 tc2
    | Ealiaspat(p, x) ->
        let tc_p = pattern p in
        let tc_n =
          let { t_typ = actual_tc } =
	    try Env.find x env with | Not_found -> print x  in
          (* every variable that is not a function has an atomic type *)
          let expected_tc = Causal.skeleton_for_variables pat.p_typ in
          less_than loc env expected_tc actual_tc;
          expected_tc in
        less_than p.p_loc env tc_n tc_p;
        tc_p in
  (* annotate the pattern with the causality type *)
  pat.p_caus <- tc;
  tc in
  pattern pat

(** Build an environment from a typing environment. *)
let build_env l_env env =
  let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } acc =
    let cur_tc = Causal.annotate (Cname n) (Causal.skeleton ty) in
    let last_tc_opt =
      match sort with
      | Smem { m_previous = true } ->
          Some(Causal.annotate (Clast n) (Causal.skeleton ty))
      | _ -> None in
    Env.add n { t_typ = cur_tc; t_last_typ = last_tc_opt } acc in
  Env.append (Env.fold entry l_env Env.empty) env
    
(** Build an environment with all entries synchronised on [c] *)
let build_env_on_c c l_env env =
  let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } acc =
    let cur_tc = Causal.annotate (Cname n) (Causal.skeleton_on_c c ty) in
    let last_tc_opt =
      match sort with
      | Smem { m_previous = true } ->
          Some(Causal.annotate (Clast n) (Causal.skeleton_on_c c ty))
      | _ -> None in
    Env.add n { t_typ = cur_tc; t_last_typ = last_tc_opt } acc in
  Env.append (Env.fold entry l_env Env.empty) env

(** Build an environment for a set of written variables *)
(* [x1:ct1;...; xn:tcn] with [cti < ct'i] where [env(xi) = ct'i] *)
let def_env loc defnames env =
    let add x acc =
      let { t_typ = tc } as tentry = Env.find x env in
      let ltc = Causal.fresh tc in
      less_than_name loc env x ltc tc;
      Env.add x { tentry with t_typ = ltc  } acc in
    let env_defnames =
      Ident.S.fold add (Deftypes.cur_names Ident.S.empty defnames) Env.empty in
    Env.append env_defnames env
  
(** Build an environment for a set of written variables *)
(* such that their causality types are *)
(* [x1:ct1[c];...; xn:tcn[c]] where [cti[c] < ct'i] *)
(* for all xi such that [env(xi) = ct'i] *)
let def_env_on_c loc defnames env c =
  let add x acc =
      let { t_typ = tc } as tentry = Env.find x env in
      let ltc = Causal.fresh_on_c c tc in
      less_than_name loc env x ltc tc;
      Env.add x { tentry with t_typ = ltc  } acc in
  let shared = Deftypes.cur_names Ident.S.empty defnames in
  let env_defnames = Ident.S.fold add shared Env.empty in
  shared, Env.append env_defnames env

(** Build an environment from [env] by replacing the causality *)
(* of [x] by its last causality for all [x in [shared\defnames]] *)
(* E.g., [match e with P1 -> x = ... | P2 -> y = ...] *)
(* with [x:a|b; y:c|d]; then [x:a|b; y:d|d] for the left branch *)
(* which means that it is analysed as if [x = ... and y = last y] *)
(* was written. *)
let last_env shared defnames env =
  let add x acc =
    let { t_typ = tc; t_last_typ = ltc_opt } = Env.find x env in
    let tc, ltc_opt =
      match ltc_opt with
      | None -> Causal.fresh tc, None | Some(ltc) -> ltc, Some(ltc) in
    Env.add x { t_typ = tc; t_last_typ = ltc_opt } acc in
  let names = Deftypes.cur_names Ident.S.empty defnames in
  let env_defnames =
    Ident.S.fold add (Ident.S.diff shared names) Env.empty in
  Env.append env_defnames env
    
(** Causality analysis of a match handler.*)
(* free variables must have a causality tag less than [c_body] *)
let match_handlers body env c_body c_e m_h_list =
  let handler { m_pat = p; m_body = b; m_env = m_env } =
    let env = build_env_on_c c_e m_env env in
    let _ = pattern env p in
    body env c_body b in
  List.map handler m_h_list
    
(** Causality analysis of a present handler *)
let present_handlers
    scondpat body env c_free c_e c_body p_h_list h_opt =
  let handler { p_cond = scpat; p_body = b; p_env = p_env } =
    (* computations in [scpat] must have a tag less than [c_e] *)
    let env = build_env p_env env in
    let actual_c = scondpat env c_free scpat in
    less_than_c scpat.loc env actual_c c_e;
    (* computations in [body] must have a tag less than [c_body] *)
    body env c_body b in
  let res_list = List.map handler p_h_list in
  match h_opt with
  | None -> res_list
  | Some(h) -> (body env c_body h) :: res_list
               
(** causality of an expression. [C | H |-cfree e: ct] *)
let rec exp env c_free ({ e_desc = desc; e_typ = ty; e_loc = loc } as e) =
  let tc = match desc with
    | Econst _ | Econstr0 _ | Eperiod _ -> Causal.skeleton ty
    | Eglobal { lname = lname } ->
        let { info = info } = Modules.find_value lname in
        Causal.instance info ty
    | Elocal(x) ->
        let { t_typ = tc } = try Env.find x env with Not_found -> print x in
        let tc = subtype true tc in
        let cset = Causal.vars S.empty tc in
        (* all elements [ci in cset] are such that [ci < c_free] *)
        S.iter (fun ci -> less_than_c loc env ci c_free) cset;
        tc
    | Elast(x) ->
        let { t_last_typ = tc_opt } =
          try Env.find x env with Not_found -> print x in
        let tc = match tc_opt with | None -> assert false | Some(tc) -> tc in
        let cset = Causal.vars S.empty tc in
        (* all elements [ci in cset] are such that [ci < c_free] *)
        S.iter (fun ci -> less_than_c loc env ci c_free) cset;
        tc
    | Econstr1(_, e_list) ->
        let c = Causal.new_var () in
        List.iter (fun e -> exp_less_than_on_c env c_free e c) e_list;
        Causal.skeleton_on_c c ty
    | Etuple(e_list) ->
        product (List.map (exp env c_free) e_list)
    | Eop(op, e_list) ->
        operator env op c_free ty e_list
    | Eapp(_, e, e_list) ->
        app env c_free (exp env c_free e) e_list
    | Erecord_access(e_record, _) ->
        let c_record = Causal.new_var () in
        exp_less_than_on_c env c_free e_record c_record;
        Causal.skeleton_on_c c_record ty
    | Erecord(l) ->
        let c_record = Causal.new_var () in
        List.iter
          (fun (_, e) -> exp_less_than_on_c env c_free e c_record) l;
        Causal.skeleton_on_c c_record ty
    | Erecord_with(e_record, l) ->
        let c_record = Causal.new_var () in
        exp_less_than_on_c env c_free e_record c_record;
        List.iter
          (fun (_, e) -> exp_less_than_on_c env c_free e c_record) l;
        Causal.skeleton_on_c c_record ty
    | Etypeconstraint(e, _) -> exp env c_free e
    | Elet(l, e_let) ->
        let new_env = local env c_free l in
        let tc = exp new_env c_free e_let in
        tc
    | Eblock(b, e_block) ->
        let env = block_eq_list Ident.S.empty env c_free b in
        let tc = exp env c_free e_block in
        tc
    | Eseq(e1, e2) ->
        ignore (exp env c_free e1);
        exp env c_free e2
    | Epresent(h_e_list, e_opt) ->
        let c_body = Causal.intro_less_c c_free in
        let c_scpat = Causal.intro_less_c c_body in
        let actual_tc =
          present_handler_exp_list
            env c_free c_body c_scpat h_e_list e_opt in
        (* the result control depend on the signal patterns [scpat] *)
        on_c actual_tc c_body
    | Ematch(_, e, h_e_list) ->
        let c_body = Causal.intro_less_c c_free in
        let c_e = Causal.intro_less_c c_body in
        exp_less_than_on_c env c_free e c_e;
        let actual_tc = match_handler_exp_list env c_body c_e h_e_list in
        (* the result control depend on [e] *)
        on_c actual_tc c_body in
  (* annotate [e] with the causality type *)
  e.e_caus <- tc;
  tc
  
(** Typing an application *)
and app env c_free tc_fct arg_list =
  (* typing the list of arguments *)
  let rec args tc_fct = function
    | [] -> subtype true tc_fct
    | arg :: arg_list ->
        let tc1, tc2 = Causal.filter_arrow tc_fct in
        exp_less_than env c_free arg tc1;
        args tc2 arg_list in
  args tc_fct arg_list
    
(** Typing an operator *)
and operator env op c_free ty e_list =
  (* the type of the result *)
  let c_res = Causal.intro_less_c c_free in
  match op, e_list with
  | Eunarypre, [e] ->
      exp_less_than_on_c env c_free e (Causal.new_var ());
      Causal.skeleton_on_c c_res ty
  | Efby, [e1;e2] ->
      exp_less_than_on_c env c_free e2 (Causal.new_var ());
      exp_less_than_on_c env c_free e1 c_res;
      Causal.skeleton_on_c c_res ty
  | Eminusgreater, [e1;e2] ->
      exp_less_than_on_c env c_free e1 c_res;
      exp_less_than_on_c env c_free e2 c_res;
      Causal.skeleton_on_c c_res ty
  | Eifthenelse, [e1; e2; e3] ->
      exp_less_than_on_c env c_free e1 c_res;
      exp_less_than_on_c env c_free e2 c_res;
      exp_less_than_on_c env c_free e3 c_res;
      Causal.skeleton_on_c c_res ty
  | Eup, [e] ->
      (* [up(e)] does not depend instantaneously of itself *)
      exp_less_than_on_c env c_free e (Causal.new_var ());
      Causal.skeleton_on_c c_res ty
  | Einitial, [] ->
      Causal.skeleton_on_c c_res ty 
  | (Etest | Edisc | Ehorizon), [e] ->
      exp_less_than_on_c env c_free e c_res;
      Causal.skeleton_on_c c_res ty
  | Eaccess, [e1; e2] ->
      exp_less_than_on_c env c_free e1 c_res;
      exp_less_than_on_c env c_free e2 c_res;
      Causal.skeleton_on_c c_res ty
  | Eupdate, [e1; i; e2] ->
      exp_less_than_on_c env c_free e1 c_res;
      exp_less_than_on_c env c_free i c_res;
      exp_less_than_on_c env c_free e1 c_res;
      Causal.skeleton_on_c c_res ty
  | Eslice _, [e] ->
      exp_less_than_on_c env c_free e c_res;
      Causal.skeleton_on_c c_res ty
  | Econcat, [e1; e2] ->
      exp_less_than_on_c env c_free e1 c_res;
      exp_less_than_on_c env c_free e2 c_res;
      Causal.skeleton_on_c c_res ty
  | Eatomic, [e] ->
      let c_arg = Causal.intro_less_c c_res in
      exp_less_than_on_c env c_free e c_arg;
      Causal.skeleton_on_c c_res ty
  | _ -> assert false
    

(** Typing an expression with an expected causality *)
(* The causality tag of [e] must be less than [expected_c] *)
(* free variables in [e] must have a tag less than [c_free] *)
and exp_less_than_on_c env c_free e expected_c =
  let actual_tc = exp env c_free e in
  let expected_tc = Causal.skeleton_on_c expected_c e.e_typ in
  less_than e.e_loc env actual_tc expected_tc;
  (* annotate [e] with the causality type *)
  e.e_caus <- expected_tc

and exp_less_than env c_free e expected_tc =
  let actual_tc = exp env c_free e in
  less_than e.e_loc env actual_tc expected_tc;
  (* annotate [e] with the causality type *)
  e.e_caus <- expected_tc

(** Typing a list of equations [env |-c eq list] *)
and equation_list env c_free eq_list = List.iter (equation env c_free) eq_list

(** Typing of an equation. [env |-cfree eq] *)
and equation env c_free { eq_desc = desc; eq_write = defnames; eq_loc = loc } =
  match desc with
  | EQeq(p, e) ->
      let tc_p = pattern env p in
      exp_less_than env c_free e tc_p
  | EQpluseq(n, e) ->
      let tc_n =
        try let { t_typ = tc } = Env.find n env in tc
        with Not_found -> print n in
      exp_less_than env c_free e tc_n
  | EQder(n, e, e0_opt, h_e_list) ->
      let { t_typ = expected_tc; t_last_typ = ltc_opt } =
        try Env.find n env with | Not_found -> print n in 
      let _ = exp env c_free e in
      (match h_e_list, e0_opt with
        | [], None -> ()
        | _ ->
            let c_body = Causal.intro_less_c c_free in
            let c_e = Causal.intro_less_c c_body in
            let actual_tc =
              present_handler_exp_list env c_free c_e c_body h_e_list e0_opt in
            let actual_tc = on_c actual_tc c_body in
            less_than loc env actual_tc expected_tc;
            match e0_opt, ltc_opt with
            | Some(e0), Some(ltc) ->
                let actual_ltc = exp env c_body e0 in
                less_than e0.e_loc env actual_ltc ltc
            | _ -> ())
  | EQinit(n, e0) ->
      let { t_typ = tc_n; t_last_typ = ltc_opt } =
        try Env.find n env with | Not_found -> print n in 
      let actual_tc = exp env c_free e0 in
      less_than e0.e_loc env actual_tc tc_n;
      (match ltc_opt with
       | None -> () | Some(ltc) -> less_than e0.e_loc env actual_tc ltc)
  | EQnext(n, e, e0_opt) ->
      (* [e] does not impose a causality constraint on [n] *)
      let _ = exp env c_free e in
      let { t_typ = tc } = try Env.find n env with Not_found -> print n in
      Misc.optional_unit (fun _ e0 -> exp_less_than env c_free e0 tc) () e0_opt
  | EQautomaton(is_weak, s_h_list, se_opt) ->
      (* Typing a state expression *)
      let state env c_free c_e { desc = desc } =
        match desc with
        | Estate0 _ -> ()
        | Estate1(_, e_list) ->
            List.iter (fun e -> exp_less_than_on_c env c_free e c_e) e_list in
      (* Compute the set of names defined by a state *)
      let cur_names_in_state b trans =
        let block acc { b_write = w } = Deftypes.cur_names acc w in
        let escape acc { e_block = b_opt } = Misc.optional block acc b_opt in
        block (List.fold_left escape Ident.S.empty trans) b in
      (* Typing of handlers *)
      (* scheduling is done this way: *)
      (* - Automata with strong preemption: *)
      (*   1. compute unless conditions; *)
      (*   2. execute the corresponding handler. *)
      (* - Automata with weak preemption: *)
      (*   1. compute the body; 2. compute the next active state. *)
      (* the causality constraints must reproduce this scheduling *)
      let escape shared env c_free c_spat
          { e_cond = sc; e_block = b_opt; e_next_state = ns; e_env = e_env } =
        let env = build_env e_env env in
        let actual_c = scondpat env c_free sc in
        less_than_c sc.loc env actual_c c_spat;
        let env =
          Misc.optional
            (fun env b -> block_eq_list shared env c_free b) env b_opt in
        state env c_free c_spat ns in
      let weak shared env c_body c_trans c_scpat
          { s_body = b; s_trans = trans; s_env = s_env } =
        (* remove from [shared] names defined in the current state *)
        let shared = Ident.S.diff shared (cur_names_in_state b trans) in
        let env = build_env s_env env in
        let env = block_eq_list shared env c_body b in
        List.iter (escape shared env c_trans c_scpat) trans in
      let strong shared env c_body c_trans c_scpat
          { s_body = b; s_trans = trans; s_env = s_env } =
        (* remove from [shared] names defined in the current state *)
        let shared = Ident.S.diff shared (cur_names_in_state b trans) in
        let env = build_env s_env env in
        List.iter (escape shared env c_trans c_scpat) trans;
        ignore (block_eq_list shared env c_body b) in
      let c_automaton = Causal.intro_less_c c_free in
      Misc.optional_unit (state env c_free) c_automaton se_opt;
      (* Every branch of the automaton is considered to be executed atomically *)
      let shared, env = def_env_on_c loc defnames env c_automaton in
      (* the causality tag for the transition conditions *)
      if is_weak then
        (* first the body; then the escape condition *)
        let c_trans = Causal.intro_less_c c_automaton in
        let c_scpat = Causal.intro_less_c c_trans in
        let c_body = Causal.intro_less_c c_scpat in
        List.iter (weak shared env c_body c_body c_scpat) s_h_list
      else
        (* first the escape condition; then the body *)
        let c_body = Causal.intro_less_c c_automaton in
        let c_trans = Causal.intro_less_c c_body in
        let c_scpat = Causal.intro_less_c c_trans in
        List.iter (strong shared env c_body c_body c_scpat) s_h_list
  | EQmatch(_, e, m_h_list) ->
      let c_body = Causal.intro_less_c c_free in
      let c_e = Causal.intro_less_c c_body in
      exp_less_than_on_c env c_free e c_e;
      let shared, env = def_env_on_c loc defnames env c_body in
      (* the [match/with] is considered to be atomic, i.e., all of *)
      (* its outputs depend on all of its free variable. *)
      (* This is done by typing the body in an environment where *)
      (* [x1:ct1[cbody];...;xn:ctn[cbody]] where [cti[cbody] < ct'i] *)
      (* where env(xi) = ct'i *)
      match_handler_block_eq_list env shared c_body c_e m_h_list
  | EQpresent(p_h_list, b_opt) ->
      let c_body = Causal.intro_less_c c_free in
      let c_scpat = Causal.intro_less_c c_body in
      (* the [present/with] is considered to be executed atomically *)
      let shared, env = def_env_on_c loc defnames env c_body in
      present_handler_block_eq_list
        env shared c_free c_scpat c_body p_h_list b_opt      
  | EQreset(eq_list, e) ->
      let c_e = Causal.intro_less_c c_free in
      exp_less_than_on_c env c_free e c_e;
      (* the [reset] block is considered to be executed atomically *)
      let _, env = def_env_on_c loc defnames env c_e in
      (* do it one more so that the causality tag of defined variables *)
      (* is strictly less than [c_e] *)
      let env = def_env loc defnames env in
      equation_list env c_e eq_list
  | EQand(and_eq_list) ->
      equation_list env c_free and_eq_list 
  | EQbefore(before_eq_list) ->
      equation_list env c_free before_eq_list 
  | EQemit(n, e_opt) ->
      let c_res = Causal.new_var () in
      Misc.optional_unit
        (fun _ e -> exp_less_than_on_c env c_free e c_res) () e_opt;
      let { t_typ = expected_tc } =
        try Env.find n env with Not_found -> print n in
      let actual_tc = Causal.annotate (Cname n) (atom c_res) in
      less_than loc env actual_tc expected_tc
  | EQblock(b_eq_list) ->
      ignore (block_eq_list Ident.S.empty env c_free b_eq_list)
  | EQforall { for_index = i_list; for_init = init_list; for_body = b_eq_list;
               for_out_env = o_env } ->
      (* Build the typing environment for inputs/outputs *)
      (* and build an association table [oi out o] for all output pairs *)
      let index (io_env, oi2o) { desc = desc } =
        match desc with
        | Einput(x, e) ->
            let in_c = Causal.new_var () in
            exp_less_than_on_c env c_free e in_c;
            let tc_arg, _ = Types.filter_vec e.e_typ in
            let tc = Causal.skeleton_on_c in_c tc_arg in
            Env.add x { t_typ = tc; t_last_typ = Some(fresh tc) } io_env,
            oi2o
        | Eindex(x, e1, e2) ->
            let in_c = Causal.new_var () in
            exp_less_than_on_c env c_free e1 in_c;
            exp_less_than_on_c env c_free e2 in_c;
            let tc = Causal.skeleton_on_c in_c e1.e_typ in
            Env.add x { t_typ = tc; t_last_typ = Some(fresh tc) } io_env,
            oi2o
      | Eoutput(oi, o) ->
          let out_c = Causal.new_var () in
          let { Deftypes.t_typ = ty } = Env.find oi o_env in
          let tc = Causal.skeleton_on_c out_c ty in
          Env.add oi { t_typ = tc; t_last_typ = Some(fresh tc) } io_env,
          Env.add oi o oi2o in
      
          (* typing the initialization *)
          let init init_env { desc = desc } =
            match desc with
            | Einit_last(x, e) ->
                let tc = exp env c_free e in
                Env.add x { t_typ = fresh tc; t_last_typ = Some(tc) } init_env in
      
          (* build the typing environment for read variables from the header *)
          let io_env, oi2o =
            List.fold_left index (Env.empty, Env.empty) i_list in

          (* build the typing environment for accummulation variables *)
          let init_env = List.fold_left init Env.empty init_list in

          (* build the typing environment *)
          let env = Env.append io_env env in
          let env = Env.append init_env env in
              
          (* type the body *)
          ignore (block_eq_list Ident.S.empty env c_free b_eq_list)

(* Typing a present handler for expressions *)
(* The handler list must be non empty or [e_opt] not none *)
and present_handler_exp_list env c_free c_e c_body p_h_list e_opt =
  (* [spat -> e]: the result both depend on [spat] and [e] *)
  let tc_list =
    present_handlers scondpat exp env c_free c_e c_body p_h_list e_opt in
  Causal.suptype_list true tc_list

(* Typing a present handler for blocks *)
and present_handler_block_eq_list
    env shared c_free c_e c_body p_h_list p_h_opt =
  (* [spat -> body]: all outputs from [body] depend on [spat] *)
  ignore
    (present_handlers
       scondpat (block_eq_list shared) env c_free c_e c_body p_h_list p_h_opt)

(* Typing a match handler for expressions *)
(* The handler list must be not empty *)
and match_handler_exp_list env c_body c_e m_h_list =
  let tc_list = match_handlers exp env c_body c_e m_h_list in
  Causal.suptype_list true tc_list 

(* Typing a match handler for blocks. *)
and match_handler_block_eq_list env shared c_body c_e m_h_list =
  ignore (match_handlers (block_eq_list shared) env c_body c_e m_h_list)

(* Typing a block with a set of equations in its body. *)
(* if [defnames = {x1,..., xn} with x1:ct'1;...;xn:ct'n in env *)
(* add [x1:ct1;...;xn:ctn] st ct1 < ct'1,..., ctn < ct'n *)
(* if [x in shared\defnames, then the block is implicitly *)
(* completed with a default value. This is achieved by considering that *)
(* the causality of [x] is that of [last x] *)
and block_eq_list shared env c_free
		  { b_locals = l_list; b_body = eq_list;
		    b_env = b_env; b_write = defnames; b_loc = loc } =
  (* shared variables depend on their last causality *)
  let env = last_env shared defnames env in
  (* typing local definitions *)
  let env = List.fold_left (fun env l -> local env c_free l) env l_list in
  (* Build the typing environment for names introduced by a *)
  (* [local x1,..., xn in ...] *)
  let env = build_env b_env env in
  let env = def_env loc defnames env in
  equation_list env c_free eq_list;
  env

  
(* Typing a local declaration. Returns the extended environment *)
and local env c_free { l_eq = eq_list; l_env = l_env; l_loc = loc } =
  (* First extend the typing environment *)
  let env = build_env l_env env in
  (* Then type the body *)
  List.iter (equation env c_free) eq_list;
  env
  
(* Typing  a signal pattern. *)
and scondpat env c_free sc =
  let rec scondpat { desc = desc; loc = loc } expected_c =
    match desc with
    | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
        scondpat sc1 expected_c; scondpat sc2 expected_c
    | Econdon(sc1, e) ->
        exp_less_than_on_c env c_free e expected_c;
       scondpat sc1 expected_c
    | Econdexp(e) ->
        exp_less_than_on_c env c_free e expected_c
    | Econdpat(e, p) ->
        exp_less_than_on_c env c_free e expected_c;
        let actual_tc = pattern env p in
        let expected_tc = Causal.skeleton_on_c expected_c p.p_typ in
        less_than p.p_loc env actual_tc expected_tc in
  let expected_c = Causal.new_var () in
  scondpat sc expected_c;
  expected_c

(* The main function *)
let implementation ff { desc = desc; loc = loc } =
  try
    match desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(f, _, e) ->
       Misc.push_binding_level ();
       let tc = exp Env.empty (Causal.new_var ()) e in
       Misc.pop_binding_level ();
       let tcs = generalise tc in
       Global.set_causality (Modules.find_value (Lident.Name(f))) tcs;
       (* output the signature *)
       if !Misc.print_causality_types then Pcaus.declaration ff f tcs
    | Efundecl (f, { f_kind = k; f_atomic = atomic;
                     f_args = p_list; f_body = e; f_env = h0 }) ->
       Misc.push_binding_level ();
       let env = build_env h0 Env.empty in
       let actual_tc_list = List.map (pattern env) p_list in
       let actual_tc_res = exp env (Causal.new_var ()) e in
       let actual_tc = Causal.funtype_list actual_tc_list actual_tc_res in
       (* for an atomic node, all outputs depend on all inputs *)
       let actual_tc =
         if atomic then
           let c_res = Causal.new_var () in
           let expected_tc = Causal.fresh_on_c c_res actual_tc in
           less_than loc env actual_tc expected_tc;
           expected_tc
         else actual_tc in
       Misc.pop_binding_level ();
       let tcs = generalise actual_tc in
       (* then add the current entries in the global environment *)
       Global.set_causality (Modules.find_value (Lident.Name(f))) tcs;
       (* output the signature *)
       if !Misc.print_causality_types then Pcaus.declaration ff f tcs
  with
  | Error(loc, kind) -> message loc kind

let implementation_list ff impl_list =
  List.iter (implementation ff) impl_list;
  impl_list
