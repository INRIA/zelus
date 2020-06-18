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

(* initialization check *)

(* we do very simple check, following STTT'04, with a simple extension *)
(* for constraining the left limit (last x) in continuous systems.
 *- E.g., [init x = e] and [pre(e)] are
 *- valid if [e] is initialized.
 *- when x is declared with [init x = e], then last x is
 *- marked to be initialized with type 0 if [x = ...] at discrete instants;
 *- 1/2 otherwise. if x is not explicitly initialized, it gets type 1 *)
open Misc
open Ident
open Global
open Zelus
open Location
open Deftypes
open Definit
open Init

(* Main error message *)
type error =
  | Iless_than of ti * ti (* not (expected_ty < actual_ty) *) 
  | Iless_than_i of t * t (* not (expected_i < actual_i) *) 
  | Ilast of Ident.t (* [last x] is un-initialized *)
  | Ivar of Ident.t (* [x] is un-initialized *)
  | Ider of Ident.t (* equation [der x = ...] appear with no initialisation *)
exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin
    match kind with
    | Iless_than(expected_ti, actual_ti) ->
        Format.eprintf
          "%aInitialization error: this expression \
           has type %a@ which should be less than@ %a.@."
          output_location loc
          Pinit.ptype expected_ti Pinit.ptype actual_ti
    | Iless_than_i(expected_i, actual_i) ->
        Format.eprintf
          "%aInitialization error: this expression \
           has type@ %a which should be less than@ %a.@."
          output_location loc
          Pinit.init expected_i Pinit.init actual_i
    | Ilast(n) ->
        Format.eprintf
          "%aInitialization error: the last value of %s \
           may not be well initialized.@."
          output_location loc
          (Ident.source n)
    | Ivar(n) ->
        Format.eprintf
          "%aInitialization error: the value of %s \
           may not be well initialized.@."
          output_location loc
          (Ident.source n)
    | Ider(n) ->
        Format.eprintf
          "%aInitialization error: the derivative of %s \
           is given but it is not initialized.@."
          output_location loc
          (Ident.source n)
  end;
  raise Misc.Error

let less_than loc actual_ti expected_ti =
  try
    Init.less actual_ti expected_ti
  with
    | Init.Clash _ -> error loc (Iless_than(actual_ti, expected_ti))

let less_for_last loc n actual_i expected_i =
  try
    Init.less_i actual_i expected_i
  with
    | Init.Clash _ -> error loc (Ilast(n))

let less_for_var loc n actual_ti expected_ti =
  try
    Init.less actual_ti expected_ti
  with
    | Init.Clash _ -> error loc (Ivar(n))

(** Build an environment from a typing environment *)
(* if [x] is defined by [init x = e] then
 *- [x] is initialized; [last x: 0] if [x] declared in a discrete
 *- context; [last x: a] otherwise.
 *- when [x = e] then [1/2 < a] if the equation is activated in continuous time *)
let build_env loc is_continuous l_env env =
  let entry x { Deftypes.t_sort = sort; Deftypes.t_typ = ty } =
    match sort with
    | Smem { m_kind = Some(Cont); m_init = Noinit; m_next = None } ->
        (* if an equation [der x = ...] is given but no initialisation *)
        (* either through [init x = ...] or [x = ...], [x] is not initialized *)
        error loc (Ider(x))
    | Smem { m_init = Noinit; m_next = Some true } ->
        (* no initialization and [next x = ...]. [t_last] is useless. *)
        { t_last = ione; t_typ = Init.skeleton_on_i ione ty }
    | Smem { m_init = (InitEq | InitDecl _) } ->
        (* [x] and [last x] or [x] and [next x] *)
        (* are well initialized *)
        let lv, iv =
          if is_continuous then Init.new_var (), izero else izero, izero in
        { t_last = lv; t_typ = Init.skeleton_on_i iv ty }
    | Svar { v_default = Some _ } ->
       (* [t_last] is useless. *)
       { t_last = ione; t_typ = Init.skeleton_on_i (Init.new_var ()) ty }
    | Svar _ ->
        { t_last = izero; t_typ = Init.skeleton_on_i (Init.new_var ()) ty }
    | Smem { m_previous = true } ->
        (* [x] initialized; [last x] uninitialized *)
        { t_last = ione; t_typ = Init.skeleton_on_i izero ty }
    | Sstatic | Sval | Smem _ -> 
        (* no constraint *)
        let lv = if is_continuous then ihalf else izero in
        { t_last = lv; t_typ = Init.skeleton ty } in
  Env.fold (fun n tentry acc -> Env.add n (entry n tentry) acc) l_env env

(* Given an environment [env], returns a new one where every entry type *)
(* [ti] is subtyped into [tj] which gets 1/2 as its minimum type *)
let half env =
  let half { t_last = lv; t_typ = ti } =
    { t_last = Init.half_i true lv; t_typ = Init.halftype true ti } in
  Env.map half env
    
(** Build an environment from [env] by replacing the initialization *)
(* type of [x] by the initialization of its last value for all *)
(* [x in [shared\defnames] *)
(* this is because an absent definition for [x] in the current branch *)
(* is interpreted as if there were an equation [x = last x] *)
(* or [x = default_x] if [x] is declared with a default value *)
let last_env shared defnames env =
  let add n acc =
    let { t_typ = ti; t_last = i } = Env.find n env in
    Env.add n { t_typ = Init.fresh_on_i izero ti; t_last = Init.new_var () }
      acc in
  let names = Deftypes.cur_names Ident.S.empty defnames in
  let env_defnames =
    Ident.S.fold add (Ident.S.diff shared names) Env.empty in
  Env.append env_defnames env

(* Names from the set [last_names] are considered to be initialized *)
let add_last_to_env is_continuous env last_names =
  let add n acc =
    let { t_typ = ti } = Env.find n env in
    let lv = if is_continuous then Init.new_var () else izero in
    Env.add n { t_typ = Init.fresh_on_i izero ti; t_last = lv } acc in
  let env_last_names =
    Ident.S.fold add last_names Env.empty in
  Env.append env_last_names env
            
(* find the initial handler from an automaton. Returns it with its complement *)
let split se_opt s_h_list =
  let statepat { desc = desc } =
    match desc with
      | Estate0pat(id) | Estate1pat(id, _) -> id in
  let state { desc = desc } =
    match desc with
      | Estate0(id) | Estate1(id, _) -> id in
  let rec splitrec s s_h_list =
    match s_h_list with
      | [] -> assert false
      | { s_state = spat } as s_h :: s_h_list -> 
          if s = statepat spat then s_h, s_h_list
          else 
            let s_h0, s_h_list = splitrec s s_h_list in
            s_h0, s_h :: s_h_list in
  match se_opt with
    | None -> (* the starting state is the first in the list *)
        List.hd s_h_list, List.tl s_h_list
    | Some(se) -> splitrec (state se) s_h_list

let print x = Misc.internal_error "unbound" Printer.name x

(** Check that partially defined names have a last value which is initialized *)
let initialized loc env shared =
  (* check that shared variable are initialialized *)
  let check n =
    let { t_typ = ti } = try Env.find n env with Not_found -> assert false in
    less_for_var loc n ti (Init.fresh_on_i izero ti) in
  Ident.S.iter check shared

(** Patterns *)
(* [pattern env p expected_ty] means that the type of [p] must be less *)
(* than [expected_ty] *)
let rec pattern is_continuous env
    ({ p_desc = desc; p_loc = loc; p_typ = ty } as p) expected_ti =
  (* annotate the pattern with the initialization type *)
  p.p_init <- expected_ti;
  match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> ()
    | Evarpat(x) -> 
        let ti1, last =
          try let { t_typ = ti1; t_last = last } = Env.find x env in ti1, last 
          with | Not_found -> assert false in
        less_than loc expected_ti ti1;
        (* an equation [x = e] in a continuous context is correct *)
        (* if x and e have the same type and [last x: t] with [1/2 <= t] *)
        if is_continuous then less_for_last loc x ihalf last
    | Econstr1pat(_, pat_list) ->
        let i = Init.new_var () in
        less_than loc expected_ti (Init.skeleton_on_i i ty);
        List.iter
          (fun p -> pattern_less_than_on_i is_continuous env p i) pat_list
    | Etuplepat(pat_list) ->
        let ty_list = Init.filter_product expected_ti in
        List.iter2 (pattern is_continuous env) pat_list ty_list
    | Erecordpat(l) -> 
        let i = Init.new_var () in
        List.iter
          (fun (_, p) -> pattern_less_than_on_i is_continuous env p i) l
    | Etypeconstraintpat(p, _) -> pattern is_continuous env p expected_ti
    | Eorpat(p1, p2) -> 
        pattern is_continuous env p1 expected_ti;
        pattern is_continuous env p2 expected_ti
    | Ealiaspat(p, n) -> 
        pattern is_continuous env p expected_ti;
        let ti_n, last = 
          try let { t_typ = ti1; t_last = last } = Env.find n env in ti1, last
          with | Not_found -> assert false in
        less_than loc expected_ti ti_n;
        if is_continuous then less_for_last loc n ihalf last

and pattern_less_than_on_i is_continuous env pat i =
  let expected_ti = Init.skeleton_on_i i pat.p_typ in
  pattern is_continuous env pat expected_ti
        
(** Match handler *)
let match_handlers is_continuous body env m_h_list =
  let handler { m_pat = pat; m_env = m_env; m_body = b } =
    let env = build_env pat.p_loc is_continuous m_env env in
    ignore (body is_continuous env b) in
  List.iter handler m_h_list

(** Present handler *)
let present_handlers is_continuous scondpat body env p_h_list =
  let handler { p_cond = scpat; p_body = b; p_env = p_env } =
    let env = build_env scpat.loc is_continuous p_env env in
    scondpat is_continuous env scpat;
    let env = if is_continuous then half env else env in
    ignore (body false env b) in
  List.iter handler p_h_list

(** Initialization of an expression *)
let rec exp is_continuous env ({ e_desc = desc; e_typ = ty } as e) =
  let ti =
    match desc with
    | Econst _ | Econstr0 _
    | Eperiod _ -> Init.skeleton_on_i (Init.new_var ()) ty
    | Eglobal { lname = lname } ->
        let { info = info } =
          try Modules.find_value lname with | Not_found -> assert false in
        Init.instance info ty
    | Elocal(x) -> 
        begin try let { t_typ = ti1 } = Env.find x env in ti1 
          with | Not_found -> print x
        end
    | Elast(x) -> 
        begin try 
            (* [last x] is initialized only if an equation [init x = e] *)
            (* appears and [e] is also initialized *)
            let { t_typ = ti; t_last = last } = Env.find x env in
            Init.fresh_on_i last ti
          with 
          | Not_found -> Init.skeleton_on_i ione ty end
    | Etuple(e_list) -> 
        product (List.map (exp is_continuous env) e_list)
    | Econstr1(_, e_list) ->
        let i = Init.new_var () in
        List.iter (fun e -> exp_less_than_on_i is_continuous env e i) e_list;
        Init.skeleton_on_i i ty
    | Eop(op, e_list) -> operator is_continuous env op ty e_list
    | Eapp(_, e, e_list) ->
        app is_continuous env (exp is_continuous env e) e_list
    | Erecord_access(e_record, _) -> 
        let i = Init.new_var () in
        exp_less_than_on_i is_continuous env e_record i;
        Init.skeleton_on_i i ty
    | Erecord(l) -> 
        let i = Init.new_var () in
        List.iter (fun (_, e) -> exp_less_than_on_i is_continuous env e i) l;
        Init.skeleton_on_i i ty
    | Erecord_with(e_record, l) -> 
        let i = Init.new_var () in
        exp_less_than_on_i is_continuous env e_record i;
        List.iter (fun (_, e) -> exp_less_than_on_i is_continuous env e i) l;
        Init.skeleton_on_i i ty
    | Etypeconstraint(e, _) -> exp is_continuous env e
    | Elet(l, e_let) -> 
        let env = local is_continuous env l in
        exp is_continuous env e_let
    | Eblock(b, e_block) ->
        let env = block_eq_list Ident.S.empty is_continuous env b in
        exp is_continuous env e_block
    | Eseq(e1, e2) -> 
        ignore (exp is_continuous env e1);
        exp is_continuous env e2
    | Epresent(p_h_list, e_opt) ->
        (* if [e] returns a tuple, all type element are synchronised, i.e., *)
        (* if one is un-initialized, the whole is un-initialized *)
        let ti = Init.skeleton_on_i (Init.new_var ()) ty in
        let _ =
          Misc.optional_map
            (fun e -> exp_less_than is_continuous env e ti) e_opt in
        present_handler_exp_list is_continuous env p_h_list ti;
        ti
    | Ematch(_, e, m_h_list) ->
        (* we force [e] to be always initialized. This is overly constraining *)
        (* but correct and simpler to justify *)
        exp_less_than_on_i is_continuous env e izero;
        let ti = Init.skeleton_on_i (Init.new_var ()) ty in
        match_handler_exp_list is_continuous env m_h_list ti;
        ti in
  (* annotate the expression with the initialization type *)
  e.e_init <- ti;
  ti
       
(** Typing an operator *)
and operator is_continuous env op ty e_list =
  match op, e_list with
  | Eunarypre, [e] -> 
      (* input of a unit delay must be of type 0 *)
      exp_less_than_on_i is_continuous env e izero; 
     Init.skeleton_on_i ione ty
  | Efby, [e1;e2] ->
      (* right input of a initialized delay must be of type 0 *)
      exp_less_than_on_i is_continuous env e2 izero;
     exp is_continuous env e1
  | Eminusgreater, [e1;e2] ->
     let t1 = exp is_continuous env e1 in
     let _ = exp is_continuous env e2 in
     t1
  | Eifthenelse, [e1; e2; e3] ->
     (* a conditional does not force all element to be initialized *)
     let i = Init.new_var () in
     exp_less_than_on_i is_continuous env e1 i;
     exp_less_than_on_i is_continuous env e2 i;
     exp_less_than_on_i is_continuous env e3 i;
     Init.skeleton_on_i i ty
  | (Einitial | Eup | Etest | Edisc
    | Eaccess | Eupdate | Eslice _ | Econcat), e_list ->
      (* here, we force the argument to be always initialized *)
      (* this is necessary for [up(x)] and access functions to arrays; not *)
      (* for the others *)
      let iv = izero in
      List.iter (fun e -> exp_less_than_on_i is_continuous env e iv) e_list;
      Init.skeleton_on_i iv ty
  | Eatomic, [e] ->
      let i = Init.new_var () in
      exp_less_than_on_i is_continuous env e i;
      Init.skeleton_on_i i ty
  | _ -> assert false


(** Typing an application *)
and app is_continuous env ti_fct arg_list =
  (* typing the list of arguments *)
  let rec args ti_fct = function
    | [] -> ti_fct
    | arg :: arg_list ->
       let ti1, ti2 = Init.filter_arrow ti_fct in
       exp_less_than is_continuous env arg ti1;
       args ti2 arg_list in
  args ti_fct arg_list

and exp_less_than_on_i is_continuous env e expected_i =
  let actual_ti = exp is_continuous env e in
  less_than e.e_loc actual_ti (Init.skeleton_on_i expected_i e.e_typ);

and opt_exp_less_than_on_i is_continuous env e_opt expected_i =
  match e_opt with
  | None -> ()
  | Some(e) -> exp_less_than_on_i is_continuous env e expected_i

and exp_less_than is_continuous env e expected_ti =
  let actual_ty = exp is_continuous env e in
  less_than e.e_loc actual_ty expected_ti;
  (* annotate the expression with the type *)


(** Checking equations *)
and equation_list is_continuous env eq_list =
  List.iter (equation is_continuous env) eq_list

and equation is_continuous env
    { eq_desc = eq_desc; eq_loc = loc; eq_write = defnames } =
  match eq_desc with
  | EQeq(p, e) -> 
      let ti = exp is_continuous env e in
      pattern is_continuous env p ti
  | EQpluseq(n, e) ->
      let ti_n =
        try let { t_typ = ti } = Env.find n env in ti
        with Not_found -> assert false in
      exp_less_than is_continuous env e ti_n
  | EQder(n, e, e0_opt, p_h_e_list) ->
      (* e must be of type 0 *)
      let ti_n, last = 
        try let { t_typ = ti1; t_last = last1 } = Env.find n env in 
          ti1, last1 
        with | Not_found -> assert false in
      exp_less_than is_continuous env e ti_n;
      less_than loc ti_n (Init.skeleton_on_i Init.izero e.e_typ);
      (match e0_opt with
       | Some(e0) -> exp_less_than_on_i false env e0 ihalf
       | None -> ()); (* less_for_last loc n last izero); *)
      present_handler_exp_list is_continuous env p_h_e_list ti_n
  | EQinit(n, e0) ->
      exp_less_than_on_i false env e0 ihalf
  | EQnext(n, e, e0_opt) ->
      (* [e] must always be well initialized *)
      exp_less_than_on_i is_continuous env e izero;
      (match e0_opt with
       | Some(e0) -> exp_less_than_on_i false env e0 ihalf
       | None -> ())
  | EQautomaton(is_weak, s_h_list, se_opt) ->
      (* state *)
      let state env { desc = desc } =
        match desc with
        | Estate0 _ -> ()
        | Estate1(_, e_list) -> 
            List.iter
              (fun e -> exp_less_than_on_i false env e izero) e_list in
      (* Compute the set of names defined by a state *)
      let cur_names_in_state b trans =
        let block acc { b_write = w } = Deftypes.cur_names acc w in
        let escape acc { e_block = b_opt } = Misc.optional block acc b_opt in
        block (List.fold_left escape Ident.S.empty trans) b in
      (* transitions *)
      let escape shared env
          { e_cond = sc; e_block = b_opt; e_next_state = ns; e_env = e_env } =
        let env = build_env sc.loc is_continuous e_env env in
        scondpat is_continuous env sc;
        let env = 
          match b_opt with
          | None -> env | Some(b) -> block_eq_list shared false env b in
        state env ns in
      (* handler *)
      let handler shared env
          { s_state = state; s_body = b; s_trans = trans; s_env = s_env } =
        (* remove from [shared] names defined in the current state *)
        let shared = Ident.S.diff shared (cur_names_in_state b trans) in
        let env = build_env state.loc is_continuous s_env env in
        let env = block_eq_list shared is_continuous env b in
        List.iter (escape shared env) trans in
      (* compute the set of shared names *)
      let shared = Deftypes.cur_names Ident.S.empty defnames in
      (* do a special treatment for the initial state *)
      let first_s_h, remaining_s_h_list = split se_opt s_h_list in
      (* first type the initial branch *)
      handler shared env first_s_h;
      (* if the initial state has only weak transition then all *)
      (* variables from [defined_names] do have a last value *)
      (* in this version of the language, weak and strong cannot be mixed *)
      let last_names =
        Deftypes.cur_names Ident.S.empty first_s_h.s_body.b_write in
      let env =
        if is_weak then add_last_to_env is_continuous env last_names else env in
      List.iter (handler shared env) remaining_s_h_list;
      (* every defined variable must be initialized *)
      initialized loc env shared;
      (* finaly check the initialisation *)
      ignore (Misc.optional_map (state env) se_opt)
  | EQmatch(total, e, m_h_list) ->
      exp_less_than_on_i is_continuous env e izero;
      let shared = Deftypes.cur_names Ident.S.empty defnames in
      match_handler_block_eq_list is_continuous shared env defnames m_h_list;
      (* every defined variable must be initialized *)
      initialized loc env shared
  | EQpresent(p_h_list, b_opt) ->
      let shared = Deftypes.cur_names Ident.S.empty defnames in
      ignore
        (Misc.optional_map
           (fun b -> ignore (block_eq_list shared is_continuous env b)) b_opt);
      present_handler_block_eq_list is_continuous shared env defnames p_h_list;
      (* every defined variable must be initialized *)
      initialized loc env shared
  | EQreset(eq_list, e) -> 
      exp_less_than_on_i is_continuous env e izero;
      equation_list is_continuous env eq_list
  | EQand(eq_list)
  | EQbefore(eq_list) -> equation_list is_continuous env eq_list
  | EQemit(n, e_opt) ->
      let ti_n = 
        try let { t_typ = ti1 } = Env.find n env in ti1
        with | Not_found -> assert false in
      less_than loc ti_n (Init.atom izero);
      ignore
        (Misc.optional_map
           (fun e -> exp_less_than_on_i is_continuous env e izero) e_opt)
  | EQblock(b_eq_list) ->
      ignore (block_eq_list Ident.S.empty is_continuous env b_eq_list)
  | EQforall { for_index = i_list; for_init = init_list; for_body = b_eq_list;
               for_in_env = i_env; for_out_env = o_env; for_loc = loc } ->
      (* typing the declaration of indexes *)
      (* all bounds must be initialized *)
      let index env { desc = desc; loc = loc } =
        match desc with
        | Einput(_, e) -> exp_less_than_on_i is_continuous env e izero
        | Eindex(_, e1, e2) ->
            exp_less_than_on_i is_continuous env e1 izero;
            exp_less_than_on_i is_continuous env e2 izero
        | Eoutput(x, xout) ->
            let ti =
              try
                let { t_typ = ti } = Env.find xout env in ti
              with | Not_found -> assert false in
            less_than loc ti (Init.atom izero) in
      (* typing the initialization *)
      (* all right hand-side expressions must be initialized *)
      let init init_env { desc = desc } =
        match desc with
        | Einit_last(x, e) ->
            let ti = exp is_continuous env e in
            let tzero = Init.skeleton_on_i izero e.e_typ in
            less_than e.e_loc ti tzero;
            Env.add x { t_last = izero; t_typ = tzero } init_env in
      List.iter (index env) i_list;
      let init_env = List.fold_left init Env.empty init_list in
      let env = build_env loc is_continuous i_env env in
      let env = build_env loc is_continuous o_env env in
      let env = Env.append init_env env in
      ignore (block_eq_list Ident.S.empty is_continuous env b_eq_list)
        
(* typing rule for a present statement where the body is an expression
 *- if [is_continuous = true] this means that every handler [ze -> body]
 *- is necessarily activated on a zero-crossing instant, thus discretely.
 *- in that case, it is enough that the body has type 1/2 and the whole
 *- present expression will get type 0 *)
and present_handler_exp_list is_continuous env p_h_list ty =
  present_handlers is_continuous scondpat 
    (fun is_continuous env e -> exp_less_than is_continuous env e ty)
    env p_h_list

(* typing of a block of equations *)
and present_handler_block_eq_list is_continuous shared env defnames p_h_list =
  present_handlers is_continuous scondpat 
    (block_eq_list shared) env p_h_list

and match_handler_block_eq_list is_continuous shared env defnames m_h_list =
  match_handlers is_continuous
    (block_eq_list shared) env m_h_list

and match_handler_exp_list is_continuous env m_h_list ty =
  match_handlers is_continuous 
    (fun is_continuous env e -> exp_less_than is_continuous env e ty)
    env m_h_list

and block_eq_list shared is_continuous env
    { b_loc = loc; b_locals = l_list; b_body = eq_list;
      b_env = b_env; b_write = defnames } =
  (* shared variables depend on their last causality *)
  let env = last_env shared defnames env in
  let env = List.fold_left (local is_continuous) env l_list in
  let env = build_env loc is_continuous b_env env in
  equation_list is_continuous env eq_list;
  env


and local is_continuous env { l_eq = eq_list; l_loc = loc; l_env = l_env } =
  (* First extend the typing environment *)
  let env = build_env loc is_continuous l_env env in
  (* then type the body *)
  List.iter (equation is_continuous env) eq_list; env
  
(* we force that the signal pattern be initialized. E.g.,
*- [present s(x) -> ...] gives the type 0 to s and x *)
and scondpat is_continuous env { desc = desc } =
  match desc with
  | Econdand(sc1, sc2) | Econdor(sc1, sc2) -> 
      scondpat is_continuous env sc1; scondpat is_continuous env sc2
  | Econdon(sc1, e) ->
      scondpat is_continuous env sc1;
      exp_less_than_on_i is_continuous env e izero
  | Econdexp(e) | Econdpat(e, _) -> 
      exp_less_than_on_i is_continuous env e izero
        
let implementation ff impl =
  try
    match impl.desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(f, _, e) ->
        (* the expression [e] must be initialized *)
        let ti_zero = Init.skeleton_on_i izero e.e_typ in
        Misc.push_binding_level ();
        exp_less_than false Env.empty e ti_zero;
        Misc.pop_binding_level ();
        let tis = generalise ti_zero in
        Global.set_init (Modules.find_value (Lident.Name(f))) tis;
        (* output the signature *)
        if !Misc.print_initialization_types then Pinit.declaration ff f tis
    | Efundecl(f, { f_kind = k; f_atomic = atomic; f_args = p_list;
                    f_body = e; f_env = h0; f_loc = loc }) -> 
        let is_continuous = match k with | C -> true | _ -> false in
        Misc.push_binding_level ();
        let env = build_env loc is_continuous h0 Env.empty in
        let ti_list = List.map (fun p -> Init.skeleton p.p_typ) p_list in
        List.iter2 (pattern is_continuous env) p_list ti_list;
        let ti_res = exp is_continuous env e in
        let actual_ti = funtype_list ti_list ti_res in
        (* for an atomic node, all outputs depend on all inputs *)
        let expected_ti =
          funtype_list (List.map (fun p -> Init.skeleton p.p_typ) p_list)
            (Init.skeleton e.e_typ) in
        less_than impl.loc actual_ti expected_ti;
        Misc.pop_binding_level ();
        let tis = generalise actual_ti in
        Global.set_init (Modules.find_value (Lident.Name(f))) tis;
        (* output the signature *)
        if !Misc.print_initialization_types then Pinit.declaration ff f tis
  with
  | Error(loc, kind) -> message loc kind
                          
let implementation_list ff impl_list =
  List.iter (implementation ff) impl_list; impl_list
