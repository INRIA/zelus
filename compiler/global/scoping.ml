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
(* scoping. introduces unique indexes for local names and replace global   *)
(* names by qualified names *)
(* the module checks the following: *)
(* - every pattern and record is linear *)
(* - name states in automata are defined once. *)
(* - local names are binded. *)

open Misc
open Location
open Parsetree
open Ident
open Deftypes
open Format

module Error =
struct
  type error =
    | Evar of string
    | Enon_linear_pat of string
    | Enon_linear_record of string
    | Enon_linear_automaton of string
    | Eautomaton_with_mixed_transitions
    | Emissing_in_orpat of string
    | Ecannot_be_set of bool * string
    | Ederivative_without_initialization of string
      
  exception Error of location * error

  let error loc kind = raise (Error(loc, kind))

  let message loc kind =
    begin match kind with
      | Evar(name) ->
          eprintf "%aScoping error: The value identifier %s is unbound.@."
            output_location loc name
      | Enon_linear_pat(name) ->
          eprintf "%aScoping error: The variable %s is bound several times in this pattern.@."
            output_location loc name
      | Emissing_in_orpat(name) ->
          eprintf
            "%aScoping error: The variable %s must occur on both sides of this pattern.@."
            output_location loc name
      | Enon_linear_record(name) ->
          eprintf "%aScoping error: The label %s is defined several times.@."
            output_location loc name
      | Enon_linear_automaton(name) ->
          eprintf
            "%aScoping error: the state %s is defined several times in this automaton.@."
            output_location loc name
      | Eautomaton_with_mixed_transitions ->
	 eprintf
	   "%aScoping error: this automaton mixes weak and strong transitions.@."
	   output_location loc
      | Ecannot_be_set(is_next, name) ->
	  eprintf "%aScoping error: the %s value of %s cannot be set. This is either \
               because the %s value is set or the last value is used.@."
        output_location loc
        (if is_next then "next" else "current")
	name
	(if is_next then "current" else "next")
      | Ederivative_without_initialization(name) ->
          eprintf
            "%aScoping error: the variable %s is defined by its derivative but lacks \
             an initialization.@."
            output_location loc name    
      end;
    raise Misc.Error
end

module S = Set.Make (struct type t = string let compare = String.compare end)

(* set of names defined in an equation. *)
type defnames = S.t

module Rename =
struct
  (* the sort of names *)
  type initialized = bool (* [init x = ...] appear *)

  (* the renaming environment associates a fresh name and a sort *)
  type value = { name: Ident.t; mutable initialized: initialized }
  include (Map.Make (struct type t = string let compare = String.compare end))
  
  (* an entry *)
  let entry n = { name = n; initialized = false }
  
  let initialize ({ initialized = s } as v) = v.initialized <- true

  (* flat an environment into a list *)
  let list env =
    fold (fun key v acc -> (key, v) :: acc) env []
  let print ff env =
    List.iter
      (fun (key, { name = n; initialized = sort }) -> 
       fprintf ff "@[%s%s@]" (if sort then "init " else "") key)
      (list env)
  
  (* build a renaming from a set of names *)
  let make names = 
    S.fold 
      (fun elt acc -> 
	let n = Ident.fresh elt in add elt (entry n) acc) names empty

  (* append env0 in front of env *)
  let append env0 env = fold (fun key v env -> add key v env) env0 env
  
  (* build a typing environment from a renaming environment *)
  (* when [init x = ...] occurs, [x] is considered to be initialized memory *)
  let typ_env env =
    let init is_init =
      if is_init then Deftypes.imemory else Deftypes.variable in
    fold 
      (fun key { name = n; initialized = is_init } acc -> 
       Env.add n { t_sort = init is_init; t_typ = no_typ } acc)
      env Env.empty
end

(* making a local declaration and a block producing a [result] *)
let emake loc desc = { (Zaux.emake desc no_typ) with Zelus.e_loc = loc }
let eqmake loc desc = { (Zaux.eqmake desc) with Zelus.eq_loc = loc }
let pmake loc desc =  { (Zaux.pmake desc no_typ) with Zelus.p_loc = loc }

let var loc x = emake loc (Zelus.Elocal(x))
let varpat loc x = pmake loc (Zelus.Evarpat(x))

let eblock eq_list = 
  { Zelus.b_vars = []; Zelus.b_locals = [];  Zelus.b_body = eq_list;
    Zelus.b_loc = no_location; Zelus.b_write = empty;
    Zelus.b_env = Env.empty; }

let block_with_result emit ({ Zelus.e_loc = loc } as e) =
  { Zelus.b_vars = [];
    Zelus.b_locals = [];
    Zelus.b_body = [emit e];
    Zelus.b_loc = loc;
    Zelus.b_write = empty;
    Zelus.b_env = Env.empty; }

let local_with_result result eq = 
  { Zelus.l_eq = [eq]; Zelus.l_loc = eq.Zelus.eq_loc; 
    Zelus.l_env =
      Env.singleton result { t_sort = Deftypes.variable; t_typ = no_typ } }

let local_for_present loc is_mem result eq_list = 
  let sort = if is_mem then Deftypes.imemory else Deftypes.variable in
  { Zelus.l_eq = eq_list; Zelus.l_loc = loc; 
    Zelus.l_env = Env.singleton result { t_sort = sort; t_typ = no_typ } }
                
let equation_with_result result ({ Zelus.e_loc = loc } as e) = 
  eqmake loc (Zelus.EQeq(varpat loc result, e))
  
let name_with_sort initialize loc env n =
  try
    let { Rename.name = m } as v = Rename.find n env in
    if initialize then v.Rename.initialized <- true;
    m
  with
  | Not_found -> Error.error loc (Error.Evar(n))

let name loc env n = name_with_sort false loc env n

let shortname = function | Name(n) -> n | Modname({ id = id }) -> id

let longname = function
  | Name(n) -> Lident.Name(n)
  | Modname({ qual = q; id = id }) ->
      Lident.Modname({ Lident.qual = q; Lident.id = id })

let immediate = function
  | Parsetree.Eint(i) -> Deftypes.Eint(i)
  | Parsetree.Ebool(b) -> Deftypes.Ebool(b)
  | Parsetree.Efloat(f) -> Deftypes.Efloat(f)
  | Parsetree.Echar(c) -> Deftypes.Echar(c)
  | Parsetree.Estring(s) -> Deftypes.Estring(s)
  | Parsetree.Evoid -> Deftypes.Evoid

let constant = function
  | Parsetree.Cimmediate(i) -> Deftypes.Cimmediate(immediate i)
  | Parsetree.Cglobal(ln) -> Deftypes.Cglobal(longname ln)

let default = function
  | Parsetree.Init(c) -> Zelus.Init(constant c)
  | Parsetree.Default(c) -> Zelus.Default(constant c)
    
let operator loc env = function
  | Eunarypre -> Zelus.Eunarypre
  | Efby -> Zelus.Efby
  | Eminusgreater -> Zelus.Eminusgreater
  | Eifthenelse -> Zelus.Eifthenelse
  | Eup -> Zelus.Eup
  | Einitial -> Zelus.Einitial
  | Edisc -> Zelus.Edisc
  | Etest -> Zelus.Etest
  | Eafter(n_list) -> Zelus.Eafter(List.map (name loc env) n_list)
  | Eop(is_inline, lname) -> Zelus.Eop(is_inline, longname lname)

let period { p_phase = p1; p_period = p2 } = 
  { Zelus.p_phase = p1; Zelus.p_period = p2 }

let kind = function
  | A -> Zelus.A | AD -> Zelus.AD | C -> Zelus.C | D -> Zelus.D

let rec types ty =
  let desc = match ty.desc with
    | Etypevar(n) -> Zelus.Etypevar(n)
    | Etypetuple(ty_list) -> Zelus.Etypetuple(List.map types ty_list)
    | Etypeconstr(lname, ty_list) ->
        Zelus.Etypeconstr(longname lname, List.map types ty_list) in
    { Zelus.desc = desc; Zelus.loc = ty.loc }

(** Build a renaming environment *)
(** the list of names present in a pattern *)
(** if [check_linear = true], stop when the same name appears twice *)
let rec build check_linear acc p =
  let rec build acc p =
    match p.desc with
      | Ewildpat | Econstpat _ | Econstr0pat _ -> acc
      | Etuplepat(p_list) -> build_list check_linear acc p_list
      | Evarpat(n) ->
	  if S.mem n acc then 
	    if check_linear 
	    then Error.error p.loc (Error.Enon_linear_pat(n)) else acc
	  else S.add n acc
      | Ealiaspat(p, n) ->
	let acc = build acc p in
	S.add n acc
      | Eorpat(p1, p2) -> 
	  let orpat loc acc0 acc1 acc =
            let one key acc =
              if S.mem key acc1 then
		if S.mem key acc then
		  if check_linear 
		  then Error.error loc (Error.Enon_linear_pat(key)) else acc
		else S.add key acc
              else
		Error.error loc (Error.Emissing_in_orpat(key)) in
            S.fold one acc0 acc in
	  let acc1 = build S.empty p1 in
	  let acc2 = build S.empty p2 in
	  let acc = orpat p.loc acc1 acc2 acc in
	  acc
      | Etypeconstraintpat(p, ty) -> build acc p
      | Erecordpat(l_p_list) -> build_record_list p.loc acc l_p_list
	
  and build_record_list loc acc label_pat_list =
    let rec buildrec acc labels label_pat_list =
      match label_pat_list with
	| [] -> acc
	| (lname, pat_label) :: label_pat_list ->
	  (* checks that the label appears only once *)
          let label = shortname lname in
          if S.mem label labels
          then Error.error loc (Error.Enon_linear_record(label))
          else
            buildrec (build acc pat_label) (S.add label labels)
              label_pat_list in
    buildrec acc S.empty label_pat_list in
  
  build acc p

and build_list check_linear acc p_list = 
  List.fold_left (build check_linear) acc p_list

(** Builds the set of names defined in a list of equations *)
let rec build_equation_list defnames eq_list = 
  List.fold_left build_equation defnames eq_list

and build_equation defnames eq =
  match eq.desc with
    | EQeq(pat, _) -> build false defnames pat
    | EQemit(n, _) | EQder(n, _, _, _) | EQinit(n, _)
    | EQnext(n, _, _) | EQpluseq(n, _) -> 
        if S.mem n defnames then defnames else S.add n defnames
    | EQautomaton(s_h_list, _) ->
        List.fold_left 
          (fun acc 
	    { desc = { s_block = b; s_until = until; s_unless = unless } } -> 
              build_automaton_handler acc b until unless) defnames s_h_list
    | EQmatch(_, m_h_list) ->
        List.fold_left 
          (fun acc { m_body = b } -> snd (build_block_equation_list acc b)) 
	  defnames m_h_list
    | EQifthenelse(_, b1, b2) ->
        let acc = snd (build_block_equation_list defnames b1) in
	snd (build_block_equation_list acc b2)
    | EQpresent(p_h_list, b_opt) ->
        let defnames = 
	  List.fold_left 
	    (fun acc { p_body = b } -> snd (build_block_equation_list acc b))
	    defnames p_h_list in
        Misc.optional 
	  (fun defnames b -> snd (build_block_equation_list defnames b)) 
	  defnames b_opt
    | EQreset(eq_list, e) ->
        build_equation_list defnames eq_list
    | EQblock(b) ->
        snd (build_block_equation_list defnames b)
        

and build_block_equation_list defnames 
    { desc = { b_vars = vardec_list; b_locals = l_list; b_body = eq_list };
      loc = loc } =
  (* bounded names [local x1 [init v1| default v1][with op1],...,xn in ...] *)
  let bounded_names =
    List.fold_left
      (fun acc { desc = { vardec_name = n } } -> 
        if S.mem n acc then Error.error loc (Error.Enon_linear_pat(n)) 
        else S.add n acc) S.empty vardec_list in
  let defnames1 = build_equation_list S.empty eq_list in
  bounded_names, S.union defnames (S.diff defnames1 bounded_names)

and build_automaton_handler defnames b until unless =
  let escape defnames { e_block = b_opt } =
    Misc.optional 
      (fun defnames b -> 
       snd (build_block_equation_list defnames b)) defnames b_opt in
  let def_in_until = List.fold_left escape S.empty until in
  let def_in_unless = List.fold_left escape S.empty unless in
  let bounded_names, defnames = build_block_equation_list defnames b in
  S.union defnames
	  (S.union (S.diff def_in_until bounded_names) def_in_unless)

(** Renaming of a pattern *)
let rec check_pattern acc p =
  let desc = match p.desc with
    | Ewildpat -> Zelus.Ewildpat
    | Econstpat(im) -> Zelus.Econstpat(immediate im)
    | Econstr0pat(ln) -> Zelus.Econstr0pat(longname ln)
    | Etuplepat(p_list) -> Zelus.Etuplepat(check_pattern_list acc p_list)
    | Evarpat(n) -> Zelus.Evarpat(name p.loc acc n)
    | Ealiaspat(p, n) ->
        Zelus.Ealiaspat(check_pattern acc p, name p.loc acc n)
    | Eorpat(p1, p2) ->
        Zelus.Eorpat(check_pattern acc p1, check_pattern acc p2)
    | Etypeconstraintpat(p, ty) ->
        Zelus.Etypeconstraintpat(check_pattern acc p, types ty)
    | Erecordpat(l_p_list) ->
        Zelus.Erecordpat
        (List.map (fun (lname, p) -> (longname lname, check_pattern acc p)) l_p_list) in
  { Zelus.p_desc = desc; Zelus.p_loc = p.loc; Zelus.p_typ = Deftypes.no_typ; Zelus.p_caus = [] }

and check_pattern_list acc p_list = List.map (check_pattern acc) p_list

(* renaming a pattern. Build the renaming environment then rename the pattern *)
let pattern env p =
  let acc = build true S.empty p in
  let env0 = Rename.make acc in
  let env = Rename.append env0 env in
  env0, env, check_pattern env0 p

and pattern_list env p_list =
  let acc = build_list true S.empty p_list in
  let env0 = Rename.make acc in
  let p_list = List.map (check_pattern env0) p_list in
  let env = Rename.append env0 env in
  env0, env, p_list

(** Two generic functions for control blocks (present/match) *)
let match_handler_list body env_pat env m_h_list =
  (* treat one handler *)
  let handler { m_pat = p; m_body = b } =
    let env_p, env, p = pattern env p in
    let b = body env_pat env b in
    { Zelus.m_pat = p; Zelus.m_body = b; 
      Zelus.m_env = Rename.typ_env env_p; 
      Zelus.m_reset = false; Zelus.m_zero = false } in
  List.map handler m_h_list

let present_handler_list scondpat body env_pat env p_h_list =
  (* treat one handler *)
  let handler { p_cond = scpat; p_body = b } =
    let env_scpat, env, scpat = scondpat env scpat in
    let b = body env_pat env b in
    { Zelus.p_cond = scpat; Zelus.p_body = b;
      Zelus.p_env = Rename.typ_env env_scpat; Zelus.p_zero = false } in
  List.map handler p_h_list

(** Translate automata *)
let state_handler_list 
    loc scondpat block_body block_in_escape expression env_pat env s_h_list se_opt =
  (* build the environment of states and check that states are not defined twice *)
  let addname acc { desc = { s_state = statepat } } =
    match statepat.desc with
    | Estate0pat(n) | Estate1pat(n, _) ->
        let m = Ident.fresh n in
        if Rename.mem n acc then
          Error.error statepat.loc (Error.Enon_linear_automaton(n))
        else Rename.add n (Rename.entry m) acc in
  let env_for_states = List.fold_left addname Rename.empty s_h_list in

  let statepat env spat =
    let env_scpat, env, desc = match spat.desc with
      | Estate0pat(n) ->
         Rename.empty, env, Zelus.Estate0pat(name spat.loc env_for_states n)
      | Estate1pat(n, n_list) ->
         let build acc n =
	   if S.mem n acc then Error.error spat.loc (Error.Enon_linear_pat(n))
	   else S.add n acc in
	 let acc = List.fold_left build S.empty n_list in
	 let env0 = Rename.make acc in
	 let n_list = List.map (fun n -> name spat.loc env0 n) n_list in
	 let env = Rename.append env0 env in
	 env0, env, Zelus.Estate1pat(name spat.loc env_for_states n, n_list) in
    env_scpat, env, { Zelus.desc = desc; Zelus.loc = spat.loc } in

  (* one state expression *)
  let state env se =
    let desc = match se.desc with
      | Estate0(n) -> Zelus.Estate0(name se.loc env_for_states n)
      | Estate1(n, e_list) -> Zelus.Estate1(name se.loc env_for_states n,
            List.map (expression env) e_list) in
    { Zelus.desc = desc; Zelus.loc = se.loc } in

  (* one escape *)
  let escape env 
      { e_cond = scpat; e_reset = r; e_block = b_opt; e_next_state = se } =
    let env_scpat, env, scpat = scondpat env scpat in
    let env, b_opt =
      match b_opt with 
	| None -> env, None 
	| Some(b) -> let env, b = block_in_escape env_pat env b in env, Some(b) in
    let se = state env se in
    { Zelus.e_cond = scpat; Zelus.e_reset = r; Zelus.e_block = b_opt;
      Zelus.e_next_state = se; Zelus.e_env = Rename.typ_env env_scpat;
      Zelus.e_zero = false } in

  (* We forbid until and unless transitions to be mixed *)
  let is_weak, is_strong =
    List.fold_left
      (fun (is_weak, is_strong)
	   { desc = { s_until = until; s_unless = unless } } ->
	     is_weak || (until <> []), is_strong || (unless <> []))
      (false, false) s_h_list in
  if is_weak && is_strong
  then Error.error loc (Error.Eautomaton_with_mixed_transitions);
  (* treat one handler *)
  let handler
	{ desc = { s_state = spat; s_block = b;
		   s_until = until; s_unless = unless }; loc = loc } =
    let env_spat, env, spat = statepat env spat in
    let new_env, b = block_body env_pat env b in
    let unless = List.map (escape env) unless in
    let until = List.map (escape new_env) until in
    { Zelus.s_loc = loc; Zelus.s_state = spat; Zelus.s_body = b; 
      Zelus.s_trans = until @ unless;
      Zelus.s_env = Rename.typ_env env_spat;
      Zelus.s_reset = false } in

  (* in case there is no transition, the automaton is weak *)
  let is_weak = not is_strong in
  is_weak, List.map handler s_h_list, Misc.optional_map (state env) se_opt

(* A block [b] appears in a context of the form [pat -> b] *)
(* [env_pat] is the environment for [pat]; [env] is the global environment *)
let block locals body env_pat env 
    { desc = { b_vars = vardec_list; b_locals = l_list; b_body = b };
      loc = loc } =
  (* hide [vardec_list] in [env_pat] as it is local *)
  let env_n_m_list, vardec_list =
    List.fold_left
      (fun (env_n_m_list, vardec_list)
	{ desc = { vardec_name = n; vardec_default = d_opt;
		   vardec_combine = c_opt }; loc = loc } ->
	  let m = Ident.fresh n in
	  let d_opt = Misc.optional_map default d_opt in
	  let c_opt = Misc.optional_map longname c_opt in
	  let vardec =
	    { Zelus.vardec_name = m;
	      Zelus.vardec_default = d_opt; Zelus.vardec_combine = c_opt;
	      Zelus.vardec_loc = loc } in
	  Rename.add n (Rename.entry m) env_n_m_list,
	  vardec :: vardec_list)
      (Rename.empty, []) vardec_list in
  let env_pat = Rename.append env_n_m_list env_pat in
  let env = Rename.append env_n_m_list env in
  (* renames local lets *)
  let env, l_list = locals env l_list in
  let b = body env_pat env b in
  env, { Zelus.b_vars = vardec_list; Zelus.b_locals = l_list; Zelus.b_body = b;
         Zelus.b_loc = loc; Zelus.b_write = empty;
         Zelus.b_env = Rename.typ_env env_n_m_list }

(** Scoping an expression *)
let rec expression env { desc = desc; loc = loc } =
  let desc = match desc with
    | Econst(i) -> Zelus.Econst (immediate i)
    | Econstr0(lname) -> Zelus.Econstr0(longname lname)
    | Evar(Name(n)) ->
        begin try
            let { Rename.name = m } = Rename.find n env in Zelus.Elocal(m)
        with
          | Not_found -> Zelus.Eglobal(Lident.Name(n))
        end
    | Evar(lname) -> Zelus.Eglobal(longname lname)
    | Elast(n) -> Zelus.Elast(name loc env n)
    | Etuple(e_list) -> Zelus.Etuple(List.map (expression env) e_list)
    | Eapp(op, e_list) ->
        Zelus.Eapp(operator loc env op, List.map (expression env) e_list)
    | Erecord(label_e_list) ->
        let rec recordrec labels label_e_list =
          match label_e_list with
          | [] -> []
          | (lname, e) :: label_e_list ->
              (* check that labels are all different *)
              let label = shortname lname in
              if S.mem label labels
              then Error.error loc (Error.Enon_linear_record(label))
              else (longname lname, expression env e) ::
              recordrec (S.add label labels) label_e_list in
        Zelus.Erecord(recordrec S.empty label_e_list)
    | Erecord_access(e1, lname) ->
        Zelus.Erecord_access(expression env e1, longname lname)
    | Etypeconstraint(e, ty) ->
        Zelus.Etypeconstraint(expression env e, types ty)
    | Elet(is_rec, eq_list, e_let) ->
        let env_p, env, eq_list = letin is_rec env eq_list in
        Zelus.Elet({ Zelus.l_eq = eq_list; 
                      Zelus.l_loc = loc; 
                      Zelus.l_env = Rename.typ_env env_p },
                    expression env e_let)
    | Eseq(e1, e2) ->
        Zelus.Eseq(expression env e1, expression env e2)
    | Eperiod(p) -> Zelus.Eperiod(period p)
    (* control structures are turned into equations *)
    | Ematch(e1, handlers) ->
        (* match e with P -> e1 => 
           let match e with P -> do result = e1 done in result *)
        let result = Ident.fresh "result" in
        let emit e = 
	  eqmake e.Zelus.e_loc (Zelus.EQeq(varpat e.Zelus.e_loc result, e)) in
	let e1 = expression env e1 in
        let handlers = 
	  match_handler_list 
	    (fun _ env e -> let e = expression env e in block_with_result emit e) 
	    Rename.empty env handlers in
	let eq = eqmake loc (Zelus.EQmatch(ref false, e1, handlers)) in
        Zelus.Elet(local_with_result result eq, var loc result)
   | Epresent(handlers, e_opt) ->
        (* Translate a present expression into a present equation *)
        (* [present sc1 -> e1 | ... else e] into *)
        (* [let present sc1 -> do res = e1 done | ... else do res = e in res] *)
        (* [present sc1 -> e1 | ... init e] into *)
        (* [let present sc1 -> do res = e1 done | ... and init res = e in res] *)
        (* [present sc1 -> e1 ...] into *)
        (* [let present sc1 -> do emit res = e1 done] *)
        (* [emit e] returns either [emit x = e] or [x = e] according to *)
        (* the completeness of the definition. A signal is emitted when the *)
        (* present handler is not complete. *)
        let result = Ident.fresh "result" in
	let emit e =
	  match e_opt with 
	    | None -> 
	        eqmake e.Zelus.e_loc (Zelus.EQemit(result, Some(e)))
	    | Some(Init _)
	    | Some(Default _) ->
	       eqmake e.Zelus.e_loc (Zelus.EQeq(varpat e.Zelus.e_loc result, e)) in
	let handlers = 
	  present_handler_list
	    scondpat 
	    (fun _ env e -> let e = expression env e in block_with_result emit e)
	    Rename.empty env handlers in
	let b_opt, eq_init, is_mem = 
	    match e_opt with 
	      | None -> None, [], false
	      | Some(Init(e)) -> None, 
		[eqmake loc (Zelus.EQinit(result, expression env e))],
		true
	      | Some(Default(e)) -> 
		 Some(block_with_result emit (expression env e)), [], false in
	let eq_list = 
	  eqmake loc (Zelus.EQpresent(handlers, b_opt)) :: eq_init in
	Zelus.Elet(local_for_present loc is_mem result eq_list, var loc result)
    | Ereset(e_body, r) ->
       (* translated into a reset that applies to equations *)
       let e_body = expression env e_body in
	let r = expression env r in
	let result = Ident.fresh "result" in
	let eq = 
	  eqmake e_body.Zelus.e_loc
	    (Zelus.EQeq(varpat e_body.Zelus.e_loc result, e_body)) in
	let eq = eqmake loc (Zelus.EQreset([eq], r)) in
	Zelus.Elet(local_with_result result eq, var loc result)
    | Eautomaton(handlers, e_opt) ->
       (* translated into an automaton that applies to equations *)
       let result = Ident.fresh "result" in
	let emit e = 
	  eqmake e.Zelus.e_loc (Zelus.EQeq(varpat e.Zelus.e_loc result, e)) in
	let is_weak, handlers, e_opt = 
	  state_handler_list loc scondpat 
	    (block locals (fun _ env e -> let e = expression env e in [emit e]))
	    (block locals equation_list)
	    expression 
	    Rename.empty env handlers e_opt in
	let eq = eqmake loc (Zelus.EQautomaton(is_weak, handlers, e_opt)) in
	Zelus.Elet(local_with_result result eq, var loc result) in
  emake loc desc


(* renaming an equation. [env_pat] is used for renamming names *)
(* appearing in patterns while [env] is used for right-hand side expressions *)
and equation env_pat env eq_list { desc = desc; loc = loc } =
  match desc with
  | EQeq(pat, e) ->
     eqmake loc (Zelus.EQeq(check_pattern env_pat pat, expression env e)) :: eq_list
  | EQder(n, e, e0_opt, p_h_e_list) ->
     let e = expression env e in
     let e0_opt = Misc.optional_map (expression env) e0_opt in
     let p_h_e_list =
       present_handler_exp_list env_pat env p_h_e_list in
     let initialized = match e0_opt with | None -> false | Some _ -> true in
     let n = name_with_sort initialized loc env_pat n in
     eqmake loc (Zelus.EQder(n, e, e0_opt, p_h_e_list)) :: eq_list
  | EQinit(n, e0) ->
     let n = name_with_sort true loc env_pat n in
     let e0 = expression env e0 in
     eqmake loc (Zelus.EQinit(n, e0)) :: eq_list
  | EQpluseq(n, e) ->
     let n = name_with_sort false loc env_pat n in
     let e = expression env e in
     eqmake loc (Zelus.EQpluseq(n, e)) :: eq_list
  | EQnext(n, e, e0_opt) ->
     let initialized = match e0_opt with | None -> false | Some _ -> true in
     let n = name_with_sort initialized loc env_pat n in
     let e = expression env e in
     let e0_opt = Misc.optional_map (expression env) e0_opt in
     eqmake loc (Zelus.EQnext(n, e, e0_opt)) :: eq_list
  | EQemit(n, e_opt) ->
    eqmake loc
      (Zelus.EQemit(name loc env_pat n, 
		    optional_map (expression env) e_opt)) :: eq_list  
  | EQautomaton(s_h_list, se_opt) ->
     let is_weak, s_h_list, st_opt =
       state_handler_eq_list loc env_pat env s_h_list se_opt in
     eqmake loc (Zelus.EQautomaton(is_weak, s_h_list, st_opt)) :: eq_list
  | EQmatch(e, m_h_list) ->
    eqmake loc
      (Zelus.EQmatch(ref false, expression env e, 
		     match_handler_block_eq_list env_pat env m_h_list)) :: eq_list
  | EQifthenelse(e, b1, b2) ->
    let ptrue =
      pmake Location.no_location (Zelus.Econstpat(Deftypes.Ebool(true))) in
    let pfalse =
      pmake Location.no_location (Zelus.Econstpat(Deftypes.Ebool(false))) in
    eqmake loc
      (Zelus.EQmatch(ref true, expression env e,
		     [ { Zelus.m_pat = ptrue; 
			 Zelus.m_body = snd (block_eq_list env_pat env b1);
			 Zelus.m_env = Env.empty;
			 Zelus.m_reset = false; Zelus.m_zero = false };
		       { Zelus.m_pat = pfalse; 
			 Zelus.m_body = snd (block_eq_list env_pat env b2);
			 Zelus.m_env = Env.empty;
			 Zelus.m_reset = false; Zelus.m_zero = false } ]))
      :: eq_list
  | EQpresent(p_h_list, b_opt) ->
     let b_opt = optional_map (fun b -> snd (block_eq_list env_pat env b)) b_opt in
     eqmake loc
       (Zelus.EQpresent(present_handler_block_eq_list env_pat env p_h_list, b_opt))
     :: eq_list
  | EQreset(eq_r_list, e) ->
    eqmake loc
      (Zelus.EQreset(List.fold_left (equation env_pat env) [] eq_r_list, 
		     expression env e)) :: eq_list
  | EQblock(b) ->
    eqmake loc (Zelus.EQblock(snd (block_eq_list env_pat env b))) :: eq_list

and equation_list env_pat env eq_list = 
  List.fold_left (equation env_pat env) [] eq_list
  
(** Translating a sequence of local declarations *)
and local env { desc = (is_rec, eq_list); loc = loc } =
  let env_let, env, eq_list = letin is_rec env eq_list in
  env,
  { Zelus.l_eq = eq_list; Zelus.l_loc = loc; Zelus.l_env = Rename.typ_env env_let }

and locals env l = 
  match l with
  | [] -> env, []
  | lo :: l ->
      let env, lo = local env lo in
      let env, l = locals env l in
      env, lo :: l

and letin is_rec env eq_list =
  let env_let = Rename.make (build_equation_list S.empty eq_list) in
  let new_env = Rename.append env_let env in
  let env_local = if is_rec then new_env else env in
  env_let, new_env, List.fold_left (equation env_let env_local) [] eq_list


(** Translate a present and match when handlers are expressions or equations *)
and present_handler_exp_list env_pat env p_h_e_list =
  present_handler_list scondpat 
    (fun _ env e -> expression env e) env_pat env p_h_e_list

and present_handler_block_eq_list env_pat env p_h_b_eq_list =
  present_handler_list scondpat 
    (fun env_pat env b -> snd (block_eq_list env_pat env b)) env_pat env p_h_b_eq_list

and match_handler_block_eq_list env_pat env m_h_b_eq_list =
  match_handler_list 
    (fun env_pat env b -> snd (block_eq_list env_pat env b)) env_pat env m_h_b_eq_list

(** Translate a block when the body is a list of equations *)
and block_eq_list env_pat env b = block locals equation_list env_pat env b

(** Translate an automaton *)
and state_handler_eq_list loc env_pat env s_h_list se_opt =
  state_handler_list loc scondpat 
    (block locals equation_list) (block locals equation_list) expression
    env_pat env s_h_list se_opt

and scondpat env scpat =
  (* first build the set of names *)
  let rec build_scondpat acc { desc = desc; loc = loc } =
    match desc with
    | Econdand(scpat1, scpat2) -> build_scondpat (build_scondpat acc scpat1) scpat2
    | Econdor(scpat1, scpat2) ->
       let orcond loc acc0 acc1 acc =
         let one key acc =
           if S.mem key acc1 then
	     if S.mem key acc then
	       Error.error loc (Error.Enon_linear_pat(key))
	     else S.add key acc
           else
	     Error.error loc (Error.Emissing_in_orpat(key)) in
         S.fold one acc0 acc in
       let acc1 = build_scondpat S.empty scpat1 in
       let acc2 = build_scondpat S.empty scpat2 in
       let acc = orcond loc acc1 acc2 acc in
       acc
    | Econdexp _ -> acc
    | Econdpat(_, p) -> build true acc p
    | Econdon(scpat, _) -> build_scondpat acc scpat in
  (* rename *)
  let scondpat env_scpat env scpat =
    let rec scondpat { desc = desc; loc = loc } =
      let desc = match desc with
	| Econdand(scpat1, scpat2) ->
	   Zelus.Econdand(scondpat scpat1, scondpat scpat2)
	| Econdor(scpat1, scpat2) ->
	   Zelus.Econdor(scondpat scpat1, scondpat scpat2)
	| Econdexp(e) ->
           Zelus.Econdexp(expression env e)
	| Econdpat(e, p) ->
           Zelus.Econdpat(expression env e, check_pattern env_scpat p)
	| Econdon(scpat, e) ->
           Zelus.Econdon(scondpat scpat, expression env e) in
      { Zelus.desc = desc; Zelus.loc = loc } in
    scondpat scpat in
  (* first build the environment for pattern variables *)
  let acc_scpat = build_scondpat S.empty scpat in
  let env_scpat = Rename.make acc_scpat in
  let env = Rename.append env_scpat env in
  (* rename *)
  let scpat = scondpat env_scpat env scpat in
  env_scpat, env, scpat

(* type signature *)
let signature { sig_inputs = sinputs; sig_output = soutput;
                sig_kind = skind; sig_safe = ssafe } =
  { Zelus.sig_inputs = List.map types sinputs; 
    Zelus.sig_output = types soutput;
    Zelus.sig_kind = kind skind; Zelus.sig_safe = ssafe }

(* type declarations. *)
let rec type_decl tydecl =
  match tydecl with
  | Eabstract_type -> Zelus.Eabstract_type
  | Eabbrev(ty) -> Zelus.Eabbrev(types ty)
  | Evariant_type(constr_decl_list) ->
      Zelus.Evariant_type(List.map constr_decl constr_decl_list)
  | Erecord_type(n_ty_list) ->
      Zelus.Erecord_type
      (List.map (fun (n, ty) -> (n, types ty)) n_ty_list)

and constr_decl n = n

let type_decls n_params_typdecl_list =
  List.map (fun (n, pars, typdecl) -> (n, pars, type_decl typdecl))
    n_params_typdecl_list

(* main entry functions *)
let implementation imp =
  try
    let desc = match imp.desc with
      | Econstdecl(n, e) ->
          Zelus.Econstdecl(n, expression Rename.empty e)
      | Efundecl(n, k, is_atomic, p_list, e) ->
          let env_p, env, p_list = pattern_list Rename.empty p_list in
            Zelus.Efundecl(n, { Zelus.f_kind = kind k;
                                 Zelus.f_atomic = is_atomic;
                                 Zelus.f_args = p_list;
                                 Zelus.f_body = expression env e;
                                 Zelus.f_env = Rename.typ_env env_p })
      | Eopen(n) -> Zelus.Eopen(n)
      | Etypedecl(n, params, tydecl) ->
          Zelus.Etypedecl(n, params, type_decl tydecl) in
      { Zelus.desc = desc; Zelus.loc = imp.loc }
  with
    | Error.Error(loc, err) -> Error.message loc err

let implementation_list imp_list = Misc.iter implementation imp_list

let interface interf =
  try
    let desc = match interf.desc with
      | Einter_open(n) -> Zelus.Einter_open(n)
      | Einter_typedecl(n, params, tydecl) ->
          Zelus.Einter_typedecl(n, params, type_decl tydecl)
      | Einter_constdecl(n, typ) ->
          Zelus.Einter_constdecl(n, types typ)
      | Einter_fundecl(n, sig_typ) ->
          Zelus.Einter_fundecl(n, signature sig_typ) in
      { Zelus.desc = desc; Zelus.loc = interf.loc }
  with
    | Error.Error(loc, err) -> Error.message loc err

let interface_list inter_list = Misc.iter interface inter_list
