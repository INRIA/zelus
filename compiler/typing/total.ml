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

(* checks totality of definitions *)
(* when a variable is declared [last x = e] then each branch is *)
(* implicitely complemented with [x = last x] *)
(* otherwise, [x] must be defined in every branch *)

open Location
open Ident
open Zelus
open Typerrors
open Deftypes
open Types

(** Names written in a block *)
let union 
      { dv = dv1; di = di1; der = der1; nv = nv1; mv = mv1 }
      { dv = dv2; di = di2; der = der2; nv = nv2; mv = mv2 } =
  { dv = S.union dv1 dv2; di = S.union di1 di2;
    der = S.union der1 der2; nv = S.union nv1 nv2; mv = S.union mv1 mv2 }

(* add two sets of names provided they are distinct *)
let add loc 
	{ dv = dv1; di = di1; der = der1; nv = nv1; mv = mv1}
        { dv = dv2; di = di2; der = der2; nv = nv2; mv = mv2  } =
  let add k set1 set2 =
    S.fold 
      (fun elt set -> 
	if not (S.mem elt set) then S.add elt set
	else error loc (Ealready(k, elt))) set1 set2 in
  { dv = add Current dv1 dv2; di = add Initial di1 di2;
    der = add Derivative der1 der2; nv = add Next nv1 nv2;
    mv = S.union mv1 mv2; }


(* checks that every partial name defined at this level *)
(* has a last value or a default value *)
let all_last loc h set =
  let check elt =
    let ({ t_sort = sort; t_typ = ty } as tentry) =
      try Env.find elt h with | Not_found -> assert false in
    match sort with
    | Smem { m_init = (InitEq | InitDecl _); m_next = Some(true) } -> ()
    | Smem ({ m_init = (InitEq | InitDecl _) } as m) ->
       tentry.t_sort <- Smem { m with m_previous = true }
    | Svar { v_default = Some _ } -> ()
    | Sstatic | Sval | Svar { v_default = None }
    | Smem _ ->
       try
	 ignore (Types.filter_signal ty);
	 tentry.t_sort <-  variable
       with Types.Unify -> error loc (Eshould_be_a_signal(elt, ty)) in
  S.iter check set

(* [merge [set1;...;setn]] returns a set of names defined in every seti *)
(* and the set of names only defined partially *)
let rec merge local_names_list =
  let two s1 s2 =
    let total, partial = S.partition (fun elt -> S.mem elt s2) s1 in
    let partial = 
      S.fold (fun elt set -> if not (S.mem elt total) then S.add elt set
        else set)
        s2 partial in
      total, partial in
    match local_names_list with
    | [] -> S.empty, S.empty
    | [s] -> s, S.empty
    | s :: local_names_list -> 
        let total, partial1 = merge local_names_list in
        let total, partial2 = two s total in
        total, S.union partial1 partial2
  
let merge_defnames_list defnames_list =
  let split (acc_dv, acc_di, acc_der, acc_nv, acc_mv)
            { dv = dv; di = di; der = der; nv = nv; mv = mv } =
    dv :: acc_dv, di :: acc_di, der :: acc_der, nv :: acc_nv, mv :: acc_mv in
  let dv, di, der, nv, mv =
    List.fold_left split ([], [], [], [], []) defnames_list in
  let dv_total, dv_partial = merge dv in
  let di_total, di_partial = merge di in
  let der_total, der_partial = merge der in
  let nv_total, nv_partial = merge nv in
  let mv_total, mv_partial = merge mv in
  (dv_total, dv_partial), (di_total, di_partial),
  (der_total, der_partial), (nv_total, nv_partial), (mv_total, mv_total)

(* The main entry. Identify variables which are partially defined *)
let merge loc h defnames_list =
  let
    (dv_total, dv_partial), (di_total, di_partial),
    (der_total, der_partial), (nv_total, nv_partial), (mv_total, mv_partial) =
    merge_defnames_list defnames_list in
  (* every partial variable must be defined as a memory or declared with *)
  (* a default value *)
  all_last loc h (S.diff dv_partial di_total);
  (* for initialized values, all branches must give a definition *)
  if not (S.is_empty di_partial) 
  then error loc (Einit_undefined(S.choose(di_partial)));
  (* the default equation for a derivative is [der x = 0] so nothing *)
  (* has to be done *)
  add loc
      { dv = dv_partial; di = di_partial; der = der_partial;
        nv = nv_partial; mv  = mv_partial }
      { dv = dv_total; di = di_total; der = der_total;
        nv = nv_total; mv = mv_total }

(* Join two sets of names in a parallel composition. Check that names *)
(* are only defined once. Moreover, reject [der x = ...] and [x = ...] *)
let join loc
	 { dv = dv1; di = di1; der = der1; nv = nv1; mv = mv1 }
         { dv = dv2; di = di2; der = der2; nv = nv2; mv = mv2 } =
  let join k names1 names2 =
    let joinrec n acc = 
      if S.mem n names1 then error loc (Ealready(k, n)) else S.add n acc in
    S.fold joinrec names2 names1 in
  let disjoint k1 k2 names1 names2 =
    let disjointrec n = 
      if S.mem n names1 then
        error loc (Ealready_with_different_kinds(k1, k2, n)) in
    S.iter disjointrec names2 in
  disjoint Current Derivative dv1 der2;
  disjoint Current Derivative dv2 der1;
  disjoint Next Derivative nv1 der2;
  disjoint Next Derivative nv2 der1;
  disjoint Multi Derivative mv1 der2;
  disjoint Multi Derivative mv2 der1;
  { dv = join Current dv1 dv2; di = join Initial di1 di2;
    der = join Derivative der1 der2; nv = join Next nv1 nv2;
    mv = S.union mv1 mv2 }
  
(** Check that every variable defined in an automaton *)
(* has a definition or is a signal or its value can be implicitly kept *)
module Automaton =
  struct
    let statepatname statepat =
      match statepat.desc with
        | Estate0pat(n) | Estate1pat(n, _) -> n
            
    let statename state =
      match state.desc with
        | Estate0(n) | Estate1(n, _) -> n
            
    (* build an initial table associating set of names to every state *)
    type entry = 
        { e_loc: location;(* location in the source for the current block *)
          mutable e_state: Deftypes.defnames;
	     (* set of names defined in the current block *)
          mutable e_until: Deftypes.defnames;
	     (* set of names defined in until transitions *)
          mutable e_unless: Deftypes.defnames; 
	     (* set of names defined in unless transitions *)
        }

    (* the initial state is particular depending on whether or not *)
    (* it is only left with a weak transition *)
    type table = { t_initial: Ident.t * entry; t_remaining: entry Env.t }

    let table state_handlers =
      let add acc { s_state = statepat; s_loc = loc } =
        Env.add (statepatname statepat)
          { e_loc = loc;
            e_state = empty;
            e_until = empty;
            e_unless = empty } acc in
      let { s_state = statepat; s_loc = loc } = List.hd state_handlers in
      let remaining_handlers = List.tl state_handlers in
      { t_initial = 
          statepatname statepat,
        { e_loc = loc; e_state = empty; e_until = empty; e_unless = empty };
        t_remaining = List.fold_left add Env.empty remaining_handlers }    
        
    let add_state state_name defined_names 
        { t_initial = (name, entry); t_remaining = rtable }  =
      let { e_loc = loc; e_unless = trans } as e = 
        if state_name = name then entry else Env.find state_name rtable in
      let _ = add loc defined_names trans in
      e.e_state <- defined_names
          
    let add_transition is_until h state_name defined_names 
        { t_initial = (name, entry); t_remaining = rtable }  =
      let {e_loc = loc;e_state = state;e_until = until;e_unless = unless} as e = 
        if state_name = name then entry else Env.find state_name rtable in
      if is_until then
        let _ = add loc defined_names state in
        e.e_until <- merge loc h [until; defined_names]   
      else
        e.e_unless <- merge loc h [unless; defined_names]
        
    let check loc h { t_initial = (name, entry); t_remaining = rtable } =
      let defined_names_list_in_states = 
        Env.fold (fun _ { e_state = defined_names } acc -> defined_names :: acc)
          rtable [] in
      (* check that variables which are defined in some state only are *)
      (* either signals or have a last value *)
      let defined_names_in_states = 
        merge loc h (entry.e_state :: defined_names_list_in_states) in
      
      (* do the same for variables defined in transitions *)
      let defined_names_list_in_transitions = 
        Env.fold
          (fun _ { e_until = until; e_unless = unless } acc -> 
            (add loc until unless) :: acc)
          rtable [] in
      let defined_names_in_transitions = 
        merge loc h 
          ((add loc entry.e_until entry.e_unless) :: 
	      defined_names_list_in_transitions) in
      union defined_names_in_states defined_names_in_transitions

    (* check that all states of the automaton are potentially accessible *)
    let check_all_states_are_accessible loc state_handlers = 
      (* the name defined by the state declaration *)
      let def_states acc { s_state = spat } =
	let statepat { desc = desc } =
	  match desc with | Estate0pat(n) | Estate1pat(n, _) -> n in
	S.add (statepat spat) acc in
      
      (* the name defined by the call to a state *)
      let called_states acc { s_trans = escape_list } =
	let sexp { desc = desc } =
	  match desc with | Estate0(n) | Estate1(n, _) -> n in
	let escape acc { e_next_state = se } = S.add (sexp se) acc in
	List.fold_left escape acc escape_list in

      (* the initial state is reachable *)
      let init_state = def_states S.empty (List.hd state_handlers) in
      let called_states =
	List.fold_left called_states init_state state_handlers in
      let def_states = List.fold_left def_states S.empty state_handlers in
            
      let unreachable_states = S.diff def_states called_states in
      if not (S.is_empty unreachable_states)
      then warning loc (Wunreachable_state (S.choose unreachable_states))
  end
