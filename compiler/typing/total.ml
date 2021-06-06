(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
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
let union { dv = dv1 } { dv = dv2 } = { dv = S.union dv1 dv2 }

(* add two sets of names provided they are distinct *)
let add loc { dv = dv1 } { dv = dv2 } =
  let add set1 set2 =
    S.fold 
      (fun elt set -> 
	if not (S.mem elt set) then S.add elt set
	else error loc (Ealready(elt))) set1 set2 in
  { dv = add dv1 dv2 }

(* checks that every partial name defined at this level *)
(* has a last value or a default value *)
let all_last loc h set =
  let check elt =
    let ({ t_sort; t_init; t_default; t_typ } as tentry) =
      try Env.find elt h with | Not_found -> assert false in
    match t_init, t_default with
    | (Some _, _) | (_, Some _) -> ()
    | None, None ->
       try
	 ignore (Types.filter_signal t_typ);
	 tentry.t_sort <- Svar
       with Types.Unify -> error loc (Eshould_be_a_signal(elt, t_typ)) in
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
  let split (acc_dv) { dv } =
    dv :: acc_dv in
  let dv =
    List.fold_left split [] defnames_list in
  let dv_total, dv_partial = merge dv in
  (dv_total, dv_partial)

(* The main entry. Identify variables which are partially defined *)
let merge loc h defnames_list =
  let
    dv_total, dv_partial = merge_defnames_list defnames_list in
  (* every partial variable must be defined as a memory or declared with *)
  (* a default value *)
  all_last loc h dv_partial;
  add loc
      { dv = dv_partial }
      { dv = dv_total }

(* Join two sets of names in a parallel composition. Check that names *)
      (* are only defined once. *)
let join loc { dv = dv1 } { dv = dv2 } =
  let join names1 names2 =
    let joinrec n acc = 
      if S.mem n names1 then error loc (Ealready(n)) else S.add n acc in
    S.fold joinrec names2 names1 in
  { dv = join dv1 dv2 }
  
(** Check that every variable defined in an automaton *)
(* has a definition or is a signal or its value can be implicitly kept *)
module Automaton =
  struct
    let statepatname statepat =
      match statepat.desc with
        | Estate0pat(n) | Estate1pat(n, _) -> n
            
    let statenames state =
      let rec statenames acc { desc } =
        match desc with
        | Estate0(n) | Estate1(n, _) -> S.add n acc
        | Estateif(_, se1, se2) -> statenames (statenames acc se1) se2 in
      statenames S.empty state
            
    (* build an initial table associating set of names to every state *)
    type entry = 
        { e_loc: Location.t;(* location in the source for the current block *)
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
          
    let add_transition is_until h defined_names 
        { t_initial = (name, entry); t_remaining = rtable } state_name  =
      let {e_loc = loc;e_state = state;
           e_until = until;e_unless = unless} as e = 
        if state_name = name then entry else Env.find state_name rtable in
      if is_until then
        let _ = add loc defined_names state in
        e.e_until <- merge loc h [until; defined_names]   
      else
        e.e_unless <- merge loc h [unless; defined_names]
        
    let add_transitions is_until h state_names defined_names t =
      S.iter (add_transition is_until h defined_names t) state_names
        
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
	let rec sexp acc { desc = desc } =
	  match desc with
          | Estate0(n) | Estate1(n, _) -> S.add n acc
          | Estateif(_, se1, se2) -> sexp (sexp acc se1) se2 in
	let escape acc { e_next_state = se } = sexp acc se in
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
