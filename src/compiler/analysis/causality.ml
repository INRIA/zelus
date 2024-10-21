(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
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
      env: Defcaus.tentry Env.t }
	       
 and kind =
   | Cless_than of tc * tc
   | Cless_than_name of Ident.t * tc * tc

(* dependence cycle and the current typing environment *)
exception Error of Location.t * error

let error loc kind = raise (Error(loc, kind))

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
    let pat_typ = Typinfo.get_type pat.pat_info in
    let expected_tc = Causal.skeleton_on_c c pat_typ in
    (* the order [expected_tc < actual_tc] is mandatory, *)
    (* not the converse *)
    less_than pat.pat_loc env expected_tc actual_tc

  and pattern ({ pat_desc; pat_loc; pat_info } as pat) =
    let pat_typ = Typinfo.get_type pat_info in
    let tc = match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ ->
        Causal.skeleton_on_c (Causal.new_var ()) pat_typ
    | Evarpat(x) ->
       let { t_tys } =
         try Env.find x env with | Not_found -> print x in
       (* every variable that is not a function has an atomic type *)
       let expected_tc = Causal.skeleton_for_variables pat_typ in
       let actual_tc = Causal.instance t_tys pat_typ in
       less_than pat_loc env expected_tc actual_tc;
       expected_tc
    | Econstr1pat(_, pat_list) ->
        let c = Causal.new_var () in
        List.iter (fun pat -> pattern_less_than_on_c pat c) pat_list;
        Causal.skeleton_on_c c pat_typ
    | Etuplepat(pat_list) ->
        product(List.map pattern pat_list)
    | Erecordpat(l) ->
       (* from the causality point of view, a record is considered to be *)
       (* atomic *)
       let c = Causal.new_var () in
       List.iter (fun { arg } -> pattern_less_than_on_c arg c) l;
       Causal.skeleton_on_c c pat_typ
    | Etypeconstraintpat(p, _) -> pattern p
    | Eorpat(p1, p2) ->
        let tc1 = pattern p1 in
        let tc2 = pattern p2 in
        Causal.suptype true tc1 tc2
    | Ealiaspat(p, x) ->
        let tc_p = pattern p in
        let tc_n =
          let { t_tys } =
	    try Env.find x env with | Not_found -> print x  in
          (* every variable that is not a function has an atomic type *)
          let expected_tc = Causal.skeleton_for_variables pat_typ in
          let actual_tc = Causal.instance t_tys pat_typ in
          less_than pat_loc env expected_tc actual_tc;
          expected_tc in
        less_than pat_loc env tc_n tc_p;
        tc_p in
  (* annotate the pattern with the causality type *)
  pat.pat_info <- Typinfo.set_caus pat.pat_info tc;
  tc in
  pattern pat

(** Build an environment from a typing environment. *)
let build_env l_env env =
  let entry n { t_sort; t_tys = { typ_body } } acc =
    let t_tys =
      Defcaus.scheme (Causal.annotate (Cname n) (Causal.skeleton typ_body)) in
    let last_tc_opt =
      match t_sort with
      | Sort_mem _ ->
          Some(Causal.annotate (Clast n) (Causal.skeleton typ_body))
      | _ -> None in
    Env.add n { t_tys; t_last_typ = last_tc_opt } acc in
  Env.append (Env.fold entry l_env Env.empty) env
    
(** Build an environment with all entries synchronised on [c] *)
let build_env_on_c c l_env env =
  let entry n { t_tys = { typ_body }; t_sort } acc =
    let t_tys =
      Defcaus.scheme
        (Causal.annotate (Cname n) (Causal.skeleton_on_c c typ_body)) in
    let last_tc_opt =
      match t_sort with
      | Sort_mem _ ->
          Some(Causal.annotate (Clast n) (Causal.skeleton_on_c c typ_body))
      | _ -> None in
    Env.add n { t_tys; t_last_typ = last_tc_opt } acc in
  Env.append (Env.fold entry l_env Env.empty) env

(** Build an environment for a set of written variables *)
(* [x1:ct1;...; xn:tcn] with [cti < ct'i] where [env(xi) = ct'i] *)
let def_env loc defnames env =
    let add x acc =
      let { t_tys = { typ_body } as t_tys } as tentry = Env.find x env in
      let tc_copy = Causal.fresh typ_body in
      less_than_name loc env x tc_copy typ_body;
      Env.add x { tentry with t_tys = { t_tys with typ_body = tc_copy }  } acc in
    let env_defnames =
      Ident.S.fold add (Defnames.cur_names Ident.S.empty defnames) Env.empty in
    Env.append env_defnames env
  
(** Build an environment for a set of written variables *)
(* such that their causality types are *)
(* [x1:ct1[c];...; xn:tcn[c]] where [cti[c] < ct'i] *)
(* for all xi such that [env(xi) = ct'i] *)
let def_env_on_c loc defnames env c =
  let add x acc =
      let { t_tys = { typ_body } as t_tys } as tentry = Env.find x env in
      let tc_copy = Causal.fresh_on_c c typ_body in
      less_than_name loc env x tc_copy typ_body;
      Env.add x { tentry with t_tys = { t_tys with typ_body = tc_copy }  } acc in
  let shared = Defnames.cur_names Ident.S.empty defnames in
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
    let { t_tys = { typ_body }; t_last_typ = ltc_opt } = Env.find x env in
    let tc, ltc_opt =
      match ltc_opt with
      | None -> Causal.fresh typ_body, None | Some(ltc) -> ltc, Some(ltc) in
    Env.add x { t_tys = Defcaus.scheme tc; t_last_typ = ltc_opt } acc in
  let names = Defnames.cur_names Ident.S.empty defnames in
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
    scondpat body env c_free c_e c_body p_h_list default_opt =
  let handler { p_cond = scpat; p_body = b; p_env = p_env } =
    (* computations in [scpat] must have a tag less than [c_e] *)
    let env = build_env p_env env in
    let actual_c = scondpat env c_free scpat in
    less_than_c scpat.loc env actual_c c_e;
    (* computations in [body] must have a tag less than [c_body] *)
    body env c_body b in
  let res_list = List.map handler p_h_list in
  match default_opt with
  | NoDefault -> res_list
  | Init(eq) | Else(eq) -> (body env c_body eq) :: res_list

let automaton_handlers
      scondpat exp_less_than_on_c leqs
      body_state body_escape
      loc c_free is_weak defnames env s_h_list se_opt =
  (* Typing a state expression *)
  let rec state env c_free c_e { desc } =
    match desc with
    | Estate0 _ -> ()
    | Estate1(_, e_list) ->
       List.iter (fun e -> exp_less_than_on_c env c_free e c_e) e_list
    | Estateif(e, s1, s2) ->
       exp_less_than_on_c env c_free e c_e;
       state env c_free c_e s1;
       state env c_free c_e s2 in
  (* Compute the set of names defined by a state *)
  let cur_names_in_state b trans =
    let block acc { b_write } = Defnames.cur_names acc b_write in
    let escape acc { e_body } = block acc e_body in
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
        { e_cond; e_let; e_body; e_next_state; e_env } =
    let env = build_env e_env env in
    let actual_c = scondpat env c_free e_cond in
    less_than_c e_cond.loc env actual_c c_spat;
    (* typing local definitions *)
    let env = leqs env c_free e_let in
    (* then the body *)
    let env = body_escape shared env c_free e_body in
    state env c_free c_spat e_next_state in
  let weak shared env c_body c_trans c_scpat
        { s_let; s_body; s_trans; s_env } =
    (* remove from [shared] names defined in the current state *)
    let shared = Ident.S.diff shared (cur_names_in_state s_body s_trans) in
    let env = build_env s_env env in
    (* typing local definitions *)
    let env = leqs env c_body s_let in
    (* then the body *)
    let env = body_state shared env c_body s_body in
    List.iter (escape shared env c_trans c_scpat) s_trans in
  let strong shared env c_body c_trans c_scpat
        { s_let; s_body; s_trans; s_env } =
    (* remove from [shared] names defined in the current state *)
    let shared = Ident.S.diff shared (cur_names_in_state s_body s_trans) in
    let env = build_env s_env env in
    List.iter (escape shared env c_trans c_scpat) s_trans;
    (* typing local definitions *)
    let env = leqs env c_body s_let in
    (* then the body *)
    ignore (body_state shared env c_body s_body) in
  let c_automaton = Causal.intro_less_c c_free in
  Util.optional_unit (state env c_free) c_automaton se_opt;
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
    
(** causality of an expression. [C | H |-cfree e: ct] *)
let rec exp env c_free ({ e_desc; e_info; e_loc } as e) =
  let e_typ = Typinfo.get_type e_info in
  let tc = match e_desc with
    | Econst _ | Econstr0 _ -> Causal.skeleton e_typ
    | Eglobal { lname } ->
        let { info } = Modules.find_value lname in
        Causal.instance_of_global_value info e_typ
    | Evar(x) ->
        let { t_tys } = try Env.find x env with Not_found -> print x in
        let tc = Causal.instance t_tys e_typ in
        let tc = subtype true tc in
        let cset = Causal.vars S.empty tc in
        (* all elements [ci in cset] are such that [ci < c_free] *)
        S.iter (fun ci -> less_than_c e_loc env ci c_free) cset;
        tc
    | Elast { id } ->
        let { t_last_typ } =
          try Env.find id env with Not_found -> print id in
        let tc =
          match t_last_typ with | None -> assert false | Some(tc) -> tc in
        let cset = Causal.vars S.empty tc in
        (* all elements [ci in cset] are such that [ci < c_free] *)
        S.iter (fun ci -> less_than_c e_loc env ci c_free) cset;
        tc
    | Econstr1 { arg_list } ->
        let c = Causal.new_var () in
        List.iter (fun e -> exp_less_than_on_c env c_free e c) arg_list;
        Causal.skeleton_on_c c e_typ
    | Etuple(e_list) ->
        product (List.map (exp env c_free) e_list)
    | Eop(op, e_list) ->
        operator env op c_free e_typ e_list
    | Eapp { f; arg_list } ->
        app env c_free (exp env c_free f) arg_list
    | Erecord_access { arg } ->
        let c_record = Causal.new_var () in
        exp_less_than_on_c env c_free arg c_record;
        Causal.skeleton_on_c c_record e_typ
    | Erecord(l) ->
        let c_record = Causal.new_var () in
        List.iter
          (fun { arg } -> exp_less_than_on_c env c_free arg c_record) l;
        Causal.skeleton_on_c c_record e_typ
    | Erecord_with(e_record, l) ->
        let c_record = Causal.new_var () in
        exp_less_than_on_c env c_free e_record c_record;
        List.iter
          (fun { arg } -> exp_less_than_on_c env c_free arg c_record) l;
        Causal.skeleton_on_c c_record e_typ
    | Etypeconstraint(e, _) -> exp env c_free e
    | Elet(l, e_let) ->
        let new_env = leq env c_free l in
        let tc = exp new_env c_free e_let in
        tc
    | Efun(fe)  -> funexp env c_free fe
    | Epresent { handlers; default_opt } ->
       let c_body = Causal.intro_less_c c_free in
       let c_scpat = Causal.intro_less_c c_body in
       let actual_tc =
         present_handler_exp_list
           env c_free c_body c_scpat handlers default_opt in
       (* the result control depend on the signal patterns [scpat] *)
       on_c actual_tc c_body
    | Ematch { e; handlers } ->
       let c_body = Causal.intro_less_c c_free in
       let c_e = Causal.intro_less_c c_body in
       exp_less_than_on_c env c_free e c_e;
       let actual_tc = match_handler_exp_list env c_body c_e handlers in
       (* the result control depend on [e] *)
       on_c actual_tc c_body
    | Ereset(e_body, e_res) ->
       let c_e = Causal.intro_less_c c_free in
       exp_less_than_on_c env c_free e_res c_e;
       exp_less_than_on_c env c_free e_body c_e;
       Causal.skeleton_on_c c_e e_typ
    | Eassert(e_body) ->
       let c_e = Causal.intro_less_c c_free in
       exp_less_than_on_c env c_free e_body c_e;
       Causal.skeleton_on_c c_e e_typ
    | Eforloop _ ->
       Misc.not_yet_implemented "causality analysis for for-loops"
    | Esizeapp _ ->
       Misc.not_yet_implemented "causality analysis for size functions"
    | Elocal _ ->
       Misc.not_yet_implemented "causality analysis for local definitions" in
  (* annotate [e] with the causality type *)
  e.e_info <- Typinfo.set_caus e.e_info tc;
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

and funexp env c_free { f_kind; f_atomic; f_args; f_body; f_env; f_loc } =
  let env = build_env f_env env in
  let tc_list = List.map (arg env) f_args in
  let tc_res = result env f_body in
  let tc = Causal.funtype_list tc_list tc_res in
  (* for an atomic node, all outputs depend on all inputs *)
  if f_atomic then
    let c_res = Causal.new_var () in
    let expected_tc = Causal.fresh_on_c c_res tc in
    less_than f_loc env tc expected_tc;
    expected_tc
  else tc

and arg h n_list = type_of_vardec_list h n_list
  
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
     exp_less_than_on_c env c_free e (Causal.new_var ());
     Causal.skeleton_on_c c_res ty
  | Ehorizon, [e] ->
     exp_less_than_on_c env c_free e c_res;
     Causal.skeleton_on_c c_res ty
  | Eperiod, [e1; e2] ->
     exp_less_than_on_c env c_free e1 c_res;
     exp_less_than_on_c env c_free e2 c_res;
     Causal.skeleton_on_c c_res ty
  | Eseq, [e1; e2] ->
     exp_less_than_on_c env c_free e1 c_res;
     exp_less_than_on_c env c_free e2 c_res;
     Causal.skeleton_on_c c_res ty
  | Eatomic, [e] ->
     exp_less_than_on_c env c_free e c_res;
     Causal.skeleton_on_c c_res ty
  | Etest, [e] ->
     exp_less_than_on_c env c_free e c_res;
     Causal.skeleton_on_c c_res ty
  | Erun _, [e1; e2] ->
     let tc1 = exp env c_free e1 in
     let tc1, tc2 = Causal.filter_arrow tc1 in
     exp_less_than env c_free e2 tc1;
     tc2
  | _ -> assert false
    

(** Typing an expression with an expected causality *)
(* The causality tag of [e] must be less than [expected_c] *)
(* free variables in [e] must have a tag less than [c_free] *)
and exp_less_than_on_c env c_free e expected_c =
  let actual_tc = exp env c_free e in
  let ty = Typinfo.get_type e.e_info in
  let expected_tc = Causal.skeleton_on_c expected_c ty in
  less_than e.e_loc env actual_tc expected_tc;
  (* annotate [e] with the causality type *)
  e.e_info <- Typinfo.set_caus e.e_info expected_tc

and exp_less_than env c_free e expected_tc =
  let actual_tc = exp env c_free e in
  less_than e.e_loc env actual_tc expected_tc;
  (* annotate [e] with the causality type *)
  e.e_info <- Typinfo.set_caus e.e_info expected_tc

(** Typing a list of equations [env |-c eq list] *)
and equation_list env c_free eq_list = List.iter (equation env c_free) eq_list

(* Typing of an equation. [env |-c_free eq] *)
(* any fresh causality variable [c] introduced in the typing of [e] *)
(* is such that [c < c_free] *)
and equation env c_free { eq_desc; eq_write; eq_loc } =
  match eq_desc with
  | EQeq(p, e) ->
      let tc_p = pattern env p in
      exp_less_than env c_free e tc_p
  | EQinit(n, e0) ->
      let { t_tys = { typ_body }; t_last_typ } =
        try Env.find n env with | Not_found -> print n in 
      let actual_tc = exp env c_free e0 in
      less_than e0.e_loc env actual_tc typ_body;
      (match t_last_typ with
       | None -> () | Some(ltc) -> less_than e0.e_loc env actual_tc ltc)
  | EQder { id; e; e_opt; handlers } ->
      let { t_tys = { typ_body }; t_last_typ } =
        try Env.find id env with | Not_found -> print id in 
      let _ = exp env c_free e in
      let c_body = Causal.intro_less_c c_free in
      (match e_opt, t_last_typ with
       | Some(e0), Some(ltc) ->
          let actual_ltc = exp env c_body e0 in
          less_than e0.e_loc env actual_ltc ltc
       | _ -> ());
      let c_e = Causal.intro_less_c c_body in
      let actual_tc =
        present_handler_exp_list
          env c_free c_e c_body handlers NoDefault in
      let actual_tc = on_c actual_tc c_body in
      less_than eq_loc env actual_tc typ_body
  | EQemit(n, e_opt) ->
      let c_res = Causal.new_var () in
      Util.optional_unit
        (fun c_res e -> exp_less_than_on_c env c_free e c_res) c_res e_opt;
      let { t_tys = { typ_body } } =
        try Env.find n env with Not_found -> print n in
      let actual_tc = Causal.annotate (Cname n) (atom c_res) in
      less_than eq_loc env actual_tc typ_body
  | EQautomaton { is_weak; handlers; state_opt } ->
     automaton_handler_eq_list
       eq_loc c_free is_weak eq_write env handlers state_opt
  | EQif { e; eq_true; eq_false } ->
      let c_body = Causal.intro_less_c c_free in
      let c_e = Causal.intro_less_c c_body in
      exp_less_than_on_c env c_free e c_e;
      let shared, env = def_env_on_c eq_loc eq_write env c_body in
      (* the [if/then/else] is a short-cut for [match/with] *)
      let env1 = last_env shared eq_true.eq_write env in
      ignore (equation env1 c_body eq_true);
      let env2 = last_env shared eq_false.eq_write env in
      ignore (equation env2 c_body eq_false)
  | EQmatch { e; handlers } ->
      let c_body = Causal.intro_less_c c_free in
      let c_e = Causal.intro_less_c c_body in
      exp_less_than_on_c env c_free e c_e;
      let shared, env = def_env_on_c eq_loc eq_write env c_body in
      (* the [match/with] is considered to be atomic, i.e., all of *)
      (* its outputs depend on all of its free variable. *)
      (* This is done by typing the body in an environment where *)
      (* [x1:ct1[cbody];...;xn:ctn[cbody]] where [cti[cbody] < ct'i] *)
      (* where env(xi) = ct'i *)
      match_handler_eq_list env shared c_body c_e handlers
  | EQpresent { handlers; default_opt } ->
      let c_body = Causal.intro_less_c c_free in
      let c_scpat = Causal.intro_less_c c_body in
      (* the [present/with] is considered to be executed atomically *)
      let shared, env = def_env_on_c eq_loc eq_write env c_body in
      present_handler_eq_list
        env shared c_free c_scpat c_body handlers default_opt      
  | EQreset(eq, e) ->
      let c_e = Causal.intro_less_c c_free in
      exp_less_than_on_c env c_free e c_e;
      (* the [reset] block is considered to be executed atomically *)
      let _, env = def_env_on_c eq_loc eq_write env c_e in
      (* do it one more so that the causality tag of defined variables *)
      (* is strictly less than [c_e] *)
      let env = def_env eq_loc eq_write env in
      equation env c_e eq
  | EQand { eq_list } ->
      equation_list env c_free eq_list 
  | EQlocal(b_eq) ->
     ignore (block_eq Ident.S.empty env c_free b_eq)
  | EQlet(l_eq, eq) ->
     let env = leq env c_free l_eq in equation env c_free eq
  | EQassert(e) ->
     let c_e = Causal.intro_less_c c_free in
     exp_less_than_on_c env c_free e c_e
  | EQempty -> ()
  | EQforloop _ ->
     Misc.not_yet_implemented "causality analysis for for-loops"
  | EQsizefun _ ->
     Misc.not_yet_implemented "causality analysis for size functions"
  
(* Typing a present handler for expressions *)
(* The handler list must be non empty or [e_opt] not none *)
and present_handler_exp_list env c_free c_e c_body p_h_list e_opt =
  (* [spat -> e]: the result both depend on [spat] and [e] *)
  let tc_list =
    present_handlers scondpat exp env c_free c_e c_body p_h_list e_opt in
  Causal.suptype_list true tc_list

(* Typing a present handler for blocks *)
and present_handler_eq_list
    env shared c_free c_e c_body p_h_list p_h_opt =
  (* [spat -> body]: all outputs from [body] depend on [spat] *)
  (* shared variables depend on their last causality *)
  let equation env c_free ({ eq_write } as eq) =
    let env = last_env shared eq_write env in
    equation env c_free eq in
  ignore
    (present_handlers
       scondpat equation env c_free c_e c_body p_h_list p_h_opt)

(* Typing a match handler for expressions *)
(* The handler list must be not empty *)
and match_handler_exp_list env c_body c_e m_h_list =
  let tc_list = match_handlers exp env c_body c_e m_h_list in
  Causal.suptype_list true tc_list 

(* Typing a match handler for blocks. *)
and match_handler_eq_list env shared c_body c_e m_h_list =
  let equation env c_free ({ eq_write } as eq) =
    let env = last_env shared eq_write env in
    equation env c_free eq in
  ignore (match_handlers equation env c_body c_e m_h_list)

and automaton_handler_eq_list loc c_free is_weak defnames env s_h_list se_opt =
  automaton_handlers
    scondpat exp_less_than_on_c
    leqs block_eq block_eq
    loc c_free is_weak defnames env s_h_list se_opt

(* Typing a block with a set of equations in its body. *)
(* if [defnames = {x1,..., xn} with x1:ct'1;...;xn:ct'n in env *)
(* add [x1:ct1;...;xn:ctn] st ct1 < ct'1,..., ctn < ct'n *)
(* if [x in shared\defnames, then the block is implicitly *)
(* completed with a default value. This is achieved by considering that *)
(* the causality of [x] is that of [last x] *)
and block_eq shared env c_free
		  { b_body; b_env; b_write; b_loc } =
  (* shared variables depend on their last causality *)
  let env = last_env shared b_write env in
  (* Build the typing environment for names introduced by a *)
  (* [local x1,..., xn in ...] *)
  let env = build_env b_env env in
  let env = def_env b_loc b_write env in
  equation env c_free b_body;
  env
 
(* Typing a local declaration. Returns the extended environment *)
and leq env c_free { l_eq; l_env } =
  (* First extend the typing environment *)
  let env = build_env l_env env in
  (* Then type the body *)
  equation env c_free l_eq;
  env

and leqs env c_free l = List.fold_left (fun env l -> leq env c_free l) env l
  
(* Typing  a signal pattern. *)
and scondpat env c_free sc =
  let rec scondpat { desc } expected_c =
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
        let ty = Typinfo.get_type p.pat_info in
        let expected_tc = Causal.skeleton_on_c expected_c ty in
        less_than p.pat_loc env actual_tc expected_tc in
  let expected_c = Causal.new_var () in
  scondpat sc expected_c;
  expected_c

(* Computes the result type for [returns (...) eq] *)
and type_of_vardec_list env n_list =
  let type_of_vardec ({ var_name; var_info } as v) =
    let { t_tys } =
      try Env.find var_name env with Not_found -> print var_name in
    let ty = Typinfo.get_type var_info in
    let tc = Causal.instance t_tys ty in
    (* annotate with the causality type *)
    v.var_info <- Typinfo.set_caus var_info tc;
    tc in
  let tc_list = List.map type_of_vardec n_list in
  match tc_list with
  | [] -> Causal.atom(Causal.new_var ())
  | [tc] -> tc
  | _ -> Causal.product tc_list

and result env ({ r_desc } as r) =
  let tc =
    match r_desc with
    | Exp(e) -> exp env (Causal.new_var ()) e
    | Returns({ b_vars } as b) ->
       let env = block_eq Ident.S.empty env (Causal.new_var ()) b in
       type_of_vardec_list env b_vars in
  (* type annotation *)
  r.r_info <- Typinfo.set_caus r.r_info tc;
  tc
       
(* The main function *)
let implementation ff { desc = desc; loc = loc } =
  try
    match desc with
    | Eopen _ | Etypedecl _ -> ()
    | Eletdecl { d_leq } ->
       (* generalisation is done only for global declarations *)
       Misc.push_binding_level ();
       let env = leq Env.empty (new_var ()) d_leq in
       Misc.pop_binding_level ();
       let env = gen_decl env in
       Env.iter
         (fun name { t_tys } ->
           Global.set_causality
             (Modules.find_value (Lident.Name(Ident.source name))) t_tys)
         env;
       (* output the signature *)
       if !Misc.print_causality_types
       then
         Env.iter
           (fun name { t_tys } ->
             Pcaus.declaration ff (Ident.source name) t_tys) env
  with
  | Error(loc, kind) -> message loc kind

(* the main entry function *)
let program ff ({ p_impl_list } as p) =
  List.iter (implementation ff) p_impl_list;
  p

