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
(* initialization check *)

(* we do very simple check. E.g., [init x = e] and [pre(e)] are *)
(* valid if [e] is initialized. For the moment, nodes must have *)
(* all their inputs and outputs initialized *)
open Misc
open Ident
open Zelus
open Location
open Deftypes
open Definit
open Init

(** An entry in the type environment *)
type tentry = 
    { t_typ: Definit.typ; (* the init type of x *)
      t_last: bool; (* last x is initialized *) }

(** Build an environment from a typing environment *)
(* if a variable is initialized with [init x = e] then [x] does *)
(* have a last value which is initialized provided [e] is initialized *)
(* otherwise, [last x] is not initialized. *)
let build_env l_env env =
  let entry { Deftypes.t_sort = sort; Deftypes.t_typ = ty } = 
    match sort with 
    | Deftypes.Smem { Deftypes.m_init = Some _ }
    | Deftypes.Sval | Deftypes.Svar _ -> 
	 { t_last = true; t_typ = Init.skeleton_on_i izero ty }
      | _ -> { t_last = false; t_typ = Init.skeleton ty } in
  Env.fold (fun n tentry acc -> Env.add n (entry tentry) acc) l_env env

(* change the status of last variables. This is useful when typing *)
(* an automaton. Every variable defined in the initial state do have a *)
(* well initialized last value in the remaining states, provided all *)
(* transitions in the initial state are weak. *)
let add_last_to_env env { dv = dv } =
  let add n env =
    let { t_typ = typ } = Env.find n env in
    Env.add n { t_typ = typ; t_last = true } env in
  S.fold add dv env

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

(* Main error message *)
type error =
  | Elast_uninitialized of Ident.t
  | Eclash

exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin match kind with
    | Eclash ->
        Format.eprintf "%aInitialization error: this expression \
                        may not be well initialized.@."
	  output_location loc
    | Elast_uninitialized(s) ->
        Format.eprintf "%aInitialization error: the last value of name %s \
                        may not be well initialized.@."
	  output_location loc
          (Ident.source s)
  end;
  raise Misc.Error

(* Unification and sub-typing relation *)
let unify loc actual_ty expected_ty =
  try
    Init.unify actual_ty expected_ty
  with
    | Init.Unify -> error loc Eclash

let less_than loc actual_ty expected_ty =
  try
    Init.less actual_ty expected_ty
  with
    | Init.Unify -> error loc Eclash

(** Check that partially defined names have a last value which is initialized *)
let initialized_last loc env defnames_list =
  (* computes the set of names which are partially defined *)
  let
      (_, dv_partial), (_, di_partial), _ =
    Total.merge_defnames_list defnames_list in
  (* check that all of them have a well-initialized initial value *)
  let check n =
    let { t_last = last } = try Env.find n env with Not_found -> assert false in
    if not last then error loc (Elast_uninitialized(n)) in
  S.iter check dv_partial;
  S.iter check di_partial

(** Patterns *)
let rec pattern env { p_desc = desc; p_loc = loc; p_typ = ty } =
  match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> 
        Init.skeleton_on_i izero ty
    | Evarpat(x) -> 
        begin try let { t_typ = ty1 } = Env.find x env in ty1 
          with | Not_found -> Init.skeleton_on_i izero ty
        end
    | Etuplepat(pat_list) ->
        product (List.map (pattern env) pat_list)
    | Erecordpat(l) -> 
        let pattern_less_than_on_i pat i =
          let actual_ty = pattern env pat in
          less_than loc actual_ty (Init.skeleton_on_i i pat.p_typ) in
        let i = Init.new_var () in
        List.iter (fun (_, p) -> pattern_less_than_on_i p i) l;
        Init.skeleton_on_i i ty
    | Etypeconstraintpat(p, _) -> pattern env p
    | Eorpat(p1, p2) -> 
        let ty1 = pattern env p1 in
        let ty2 = pattern env p2 in
        unify p1.p_loc ty1 ty2;
        ty1
    | Ealiaspat(p, n) -> 
        let ty_p = pattern env p in
        let ty_n = 
          begin try let { t_typ = ty1 } = Env.find n env in ty1 
            with | Not_found -> Init.skeleton_on_i izero ty
          end in
        unify p.p_loc ty_p ty_n;
        ty_p

(** Blocks *)
let block locals body env { b_locals = l_list; b_body = bo; b_env = b_env } =
  (* First extend the typing environment *)
  let env = build_env b_env env in
  let env = locals env l_list in
  body env bo;
  env

(** Match handler *)
let match_handlers body env m_h_list =
  let handler { m_body = b } =
    body env b in
  List.iter handler m_h_list

(** Present handler *)
let present_handlers scondpat body env p_h_list =
  let handler { p_cond = scpat; p_body = b; p_env = h0 } =
    scondpat env scpat;
    body env b in
  List.iter handler p_h_list

(** Initialization of an expression *)
let rec exp env { e_desc = desc; e_typ = ty } =
  match desc with
    | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> 
        Init.skeleton_on_i (Init.new_var ()) ty
    | Elocal(x) -> 
        begin try let { t_typ = ty1 } = Env.find x env in ty1 
          with | Not_found -> Init.skeleton_on_i izero ty
        end
    | Elast(x) -> 
        begin try 
            (* [last x] is initialized only if an equation [init x = e] *)
            (* appears and [e] is also initialized *)
            let { t_last = last } = Env.find x env in
            if last then Init.skeleton_on_i izero ty
            else Init.skeleton_on_i ione ty 
          with 
            | Not_found -> Init.skeleton_on_i ione ty end
    | Etuple(e_list) -> 
        product (List.map (exp env) e_list)
    | Eapp(op, e_list) -> apply env op ty e_list
    | Erecord_access(e_record, _) -> 
        let i = Init.new_var () in
        exp_less_than_on_i env e_record i;
	Init.skeleton_on_i i ty
    | Erecord(l) -> 
        let i = Init.new_var () in
        List.iter (fun (_, e) -> exp_less_than_on_i env e i) l;
        Init.skeleton_on_i i ty
    | Etypeconstraint(e, _) -> exp env e
    | Elet(l, e_let) -> 
        let env = local env l in
        exp env e_let
    | Eseq(e1, e2) -> 
        ignore (exp env e1);
        exp env e2
    | Epresent(p_h_list, e_opt) ->
        let ty = Init.skeleton_on_i (Init.new_var ()) ty in
        let _ = Misc.optional_map (fun e -> exp_less_than env e ty) e_opt in
        present_handler_exp_list env p_h_list ty;
	ty
    | Ematch(_, e, m_h_list) ->
        let ty = Init.skeleton_on_i (Init.new_var ()) ty in
        exp_less_than_on_i env e izero;
        match_handler_exp_list env m_h_list ty;
	ty

(** Typing an application *)
and apply env op ty e_list =
  match op, e_list with
    | Eunarypre, [e] -> 
        exp_less_than_on_i env e izero; 
        Init.skeleton_on_i ione ty
    | Efby, [e1;e2] ->
        exp_less_than_on_i env e2 izero;
        exp env e1
    | Eminusgreater, [e1;e2] ->
        let t1 = exp env e1 in
        let _ = exp env e2 in
        t1
    | Eifthenelse, [e1; e2; e3] ->
        let i = Init.new_var () in
        exp_less_than_on_i env e1 i;
        exp_less_than_on_i env e2 i;
        exp_less_than_on_i env e3 i;
        Init.skeleton_on_i i ty
    | (Einitial | Eup | Etest | Edisc), e_list ->
        let i = Init.new_var () in
        List.iter (fun e -> exp_less_than_on_i env e izero) e_list;
        Init.skeleton_on_i i ty
    | Eop(_, lname), e_list when Types.is_a_node lname ->
        (* for the moment, no type signature is stored in the global *)
        (* environment. Arguments/results must always be initialized. *)
        List.iter (fun e -> exp_less_than_on_i env e izero) e_list;
        Init.skeleton_on_i izero ty
    | Eop(_, lname), e_list ->
        (* combinatorial functions are abstracted as the identity. Warning: *)
        (* this is only correct for functions that are safe. To be done *)
        let i = Init.new_var () in
        List.iter (fun e -> exp_less_than_on_i env e i) e_list;
        Init.skeleton_on_i i ty
    | Eevery(_, lname), e :: e_list ->
        let i = Init.new_var () in
        List.iter (fun e -> exp_less_than_on_i env e i) e_list;
        exp_less_than_on_i env e izero;
        Init.skeleton_on_i i ty
    | _ -> assert false

and exp_less_than_on_i env e expected_i =
  let actual_ty = exp env e in
  less_than e.e_loc actual_ty (Init.skeleton_on_i expected_i e.e_typ)

and opt_exp_less_than_on_i env e_opt expected_i =
  match e_opt with | None -> () | Some(e) -> exp_less_than_on_i env e expected_i

and exp_less_than env e expected_ty =
  let actual_ty = exp env e in
  less_than e.e_loc actual_ty expected_ty

(** Checking equations *)
and equation_list env eq_list = List.iter (equation env) eq_list

and equation env { eq_desc = eq_desc; eq_loc = loc } =
  match eq_desc with
    | EQeq(p, e) -> 
        let ty_p = pattern env p in
        exp_less_than env e ty_p
    | EQpluseq(n, e) ->
        let ty_n =
	  try let { t_typ = ty } = Env.find n env in ty
	  with Not_found -> assert false in
	exp_less_than env e ty_n
    | EQder(n, e, e0_opt, p_h_e_list) ->
        let ty_n, is_last = 
          begin try let { t_typ = ty1; t_last = is_last } = Env.find n env in 
		    ty1, is_last 
            with | Not_found -> assert false
          end in
        exp_less_than env e ty_n;
        (match e0_opt with
	  | None -> if not is_last then error loc (Elast_uninitialized(n))
	  | Some(e0) -> exp_less_than_on_i env e0 izero);
        present_handler_exp_list env p_h_e_list ty_n
    | EQinit(n, e0) ->
        exp_less_than_on_i env e0 izero
    | EQnext(n, e, e0_opt) ->
        let ty_n = try let { t_typ = ty } = Env.find n env in ty
		   with Not_found -> assert false in
	exp_less_than env e ty_n;
        ignore
	  (Misc.optional_map (fun e -> exp_less_than env e ty_n) e0_opt);
	unify e.e_loc ty_n (Init.skeleton_on_i izero e.e_typ)
    | EQautomaton(is_weak, s_h_list, se_opt) ->
        (* state *)
        let state env { desc = desc } =
	  match desc with
	    | Estate0 _ -> ()
	    | Estate1(_, e_list) -> 
	      List.iter (fun e -> exp_less_than_on_i env e izero) e_list in
	(* handler *)
        let handler env { s_body = b; s_trans = trans } =
          let escape env { e_cond = sc; e_block = b_opt; e_next_state = ns } =
            scondpat env sc;
	    let env = 
	      match b_opt with | None -> env | Some(b) -> block_eq_list env b in
	    state env ns in
          let env = block_eq_list env b in
          List.iter (escape env) trans in
        (* do a special treatment for the initial state *)
        let first_s_h, remaining_s_h_list = split se_opt s_h_list in
	(* first type the initial branch *)
        handler env first_s_h;
        (* if the initial state has only weak transition then all *)
        (* variables from [defined_names] do have a last value *)
        let defnames = first_s_h.s_body.b_write in
        let env = if is_weak then add_last_to_env env defnames else env in
        List.iter (handler env) remaining_s_h_list;
	(* every partially defined value must have an initialized value *)
	let defnames_list =
	  List.map (fun { s_body = { b_write = w } } -> w) remaining_s_h_list in
	initialized_last loc env (defnames :: defnames_list);
	(* finaly check the initialisation *)
	ignore (Misc.optional_map (state env) se_opt)
    | EQmatch(total, e, m_h_list) ->
        exp_less_than_on_i env e izero;
        match_handler_block_eq_list env m_h_list;
	(* every partially defined value must have an initialized value *)
	let defnames_list =
	  List.map (fun { m_body = { b_write = w } } -> w) m_h_list in
	let defnames_list = 
	  if !total then defnames_list else Deftypes.empty :: defnames_list in
	initialized_last loc env defnames_list
    | EQpresent(p_h_list, b_opt) ->
        let _ = Misc.optional_map (fun b -> ignore (block_eq_list env b)) b_opt in
        present_handler_block_eq_list env p_h_list;
	(* every partially defined value must have an initialized value *)
	let defnames =
	  match b_opt with | None -> Deftypes.empty | Some { b_write = w } -> w in
	let defnames_list =
	  List.map (fun { p_body = { b_write = w } } -> w) p_h_list in
	initialized_last loc env (defnames :: defnames_list)       
    | EQreset(eq_list, e) -> 
        exp_less_than_on_i env e izero;
        equation_list env eq_list
    | EQemit(n, e_opt) ->
        let ty_n = 
          try let { t_typ = ty1 } = Env.find n env in ty1
          with | Not_found -> assert false in
        unify loc ty_n (Init.atom izero);
	ignore
	  (Misc.optional_map (fun e -> exp_less_than_on_i env e izero) e_opt)
    | EQblock(b_eq_list) ->
       ignore (block_eq_list env b_eq_list)

and present_handler_exp_list env p_h_list ty =
  present_handlers scondpat 
    (fun env e -> exp_less_than env e ty)
    env p_h_list

and present_handler_block_eq_list env p_h_list =
  present_handlers scondpat 
    (fun env b -> ignore (block_eq_list env b))
    env p_h_list

and match_handler_block_eq_list env m_h_list =
  match_handlers
    (fun env b -> ignore (block_eq_list env b))
    env m_h_list

and match_handler_exp_list env m_h_list ty =
  match_handlers
    (fun env e -> exp_less_than env e ty)
    env m_h_list

and block_eq_list env b =
  let locals env l_list =
    List.fold_left local env l_list in
  block locals equation_list env b

and local env { l_eq = eq_list; l_loc = loc; l_env = l_env } =
  (* First extend the typing environment *)
  let env = build_env l_env env in
  (* then type the body *)
  List.iter (equation env) eq_list; env
  
and scondpat env { desc = desc } =
  match desc with
    | Econdand(sc1, sc2) | Econdor(sc1, sc2) -> 
        scondpat env sc1; scondpat env sc2
    | Econdon(sc1, e) ->
        scondpat env sc1;
        exp_less_than_on_i env e izero
    | Econdexp(e) | Econdpat(e, _) -> 
        exp_less_than_on_i env e izero

let implementation ff impl =
  try
    match impl.desc with
      | Eopen _ | Etypedecl _ -> ()
      | Econstdecl(_, e) | Efundecl(_, { f_body = e }) -> 
          exp_less_than_on_i Env.empty e izero
  with
    | Error(loc, kind) -> message loc kind

let implementation_list ff impl_list = List.iter (implementation ff) impl_list
