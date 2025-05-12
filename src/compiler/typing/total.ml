(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
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
open Defnames

(* Names written in a block *)
let union def1 def2 = Defnames.union def1 def2

(* add two sets of names provided they are distinct *)
let add loc 
	{ dv = dv1; di = di1; der = der1 }
        { dv = dv2; di = di2; der = der2 } =
  let add k set1 set2 =
    S.fold 
      (fun elt set -> 
	if not (S.mem elt set) then S.add elt set
	else error loc (Ealready(k, elt))) set1 set2 in
  { dv = add Current dv1 dv2; di = add Initial di1 di2;
    der = add Derivative der1 der2 }

(* checks that every partial name defined at this level *)
(* has a last value or a default value *)
let all_last loc h set =
  let check elt =
    let ({ t_sort; t_tys } as tentry) =
      try Env.find elt h with | Not_found -> assert false in
    let t_typ = Types.instance t_tys in
    match t_sort with
    | Sort_mem ({ m_init = Eq | Decl _ } | { m_default = Eq | Decl _ }) -> ()
    | _ ->
       try
	 ignore (Types.filter_signal t_typ);
	 tentry.t_sort <- Sort_var
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
  let split (acc_dv, acc_di, acc_der) { dv; di; der } =
    dv :: acc_dv, di :: acc_di, der :: acc_der in
  let dv, di, der =
    List.fold_left split ([], [], []) defnames_list in
  let dv_total, dv_partial = merge dv in
  let di_total, di_partial = merge di in
  let der_total, der_partial = merge der in
  (dv_total, dv_partial), (di_total, di_partial), (der_total, der_partial)

(* The main entry. Identify variables which are partially defined *)
let merge loc h defnames_list =
  let
    (dv_total, dv_partial), (di_total, di_partial), (der_total, der_partial) =
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
      { dv = dv_partial; di = di_partial; der = der_partial }
      { dv = dv_total; di = di_total; der = der_total }

(* Join two sets of names in a parallel composition. Check that names *)
(* are only defined once. Moreover, reject [der x = ...] and [x = ...] *)
let join loc
	 { dv = dv1; di = di1; der = der1 }
         { dv = dv2; di = di2; der = der2 } =
  (* let dv1_ = S.to_list dv1 in
  let dv2_ = S.to_list dv2 in
  let di1_ = S.to_list di1 in
  let di2_ = S.to_list di2 in
  let der1_ = S.to_list der1 in
  let der2_ = S.to_list der2 in *)
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
  { dv = join Current dv1 dv2; di = join Initial di1 di2;
    der = join Derivative der1 der2 }
  
(* Check that every variable defined in an automaton *)
(* has a definition or is a signal or its value can be implicitly kept *)
module Automaton =
  struct
    let state_patname statepat =
      match statepat.desc with
        | Estate0pat(n) | Estate1pat(n, _) -> n
            
    let rec state_names acc { desc } =
      match desc with
      | Estate0(n) | Estate1(n, _) -> S.add n acc
      | Estateif(_, se1, se2) -> state_names (state_names acc se1) se2
            
    (* build an initial table associating set of names to every state *)
    type entry = 
        { e_loc: Location.t;(* location in the source for the current block *)
          mutable e_defnames: Defnames.defnames;
	  (* for a state [s], the set of names defined in [s] *)
          mutable e_trans_defnames: Defnames.defnames;
	  (* for an automaton with [until] transitions, the *)
          (* set of names defined on an output transition *)
          (* belong to the source state [s] *)
          (* for an automaton with [unless] transitions, the set *)
          (* of names defined on a transition that enters target state [s'] *)
          (* belong to that state *)
          e_target_states: S.t; (* set of target states *)
        }

    type table =
      { t_weak: bool; (* kind of transitions - either all weak or all strong *)
        t_initials: entry Env.t; (* initial states of the automaton *)
        t_remaining: entry Env.t; (* other, non initial states *)
      }
    
    (* observing function for debugging purposes *)
    let to_list defnames = S.to_list (Defnames.names S.empty defnames)
    let dump { t_initials; t_remaining } =
      let entry (id, { e_defnames; e_trans_defnames }) =
        id, to_list e_defnames, to_list e_trans_defnames in
      List.map entry (Env.to_list t_initials),
      List.map entry (Env.to_list t_remaining)        

    (* get defined names associated to state name [s_name] *)
    let find s_name { t_initials; t_remaining } =
      try Env.find s_name t_initials
      with Not_found ->
        try Env.find s_name t_remaining with Not_found -> assert false
    
    let find_defined_names s_name table =
      let { e_defnames } = find s_name table in e_defnames
    
    (* the name defined by the state declaration *)
    let statepat_name_of_handler { s_state = { desc } } =
      match desc with | Estate0pat(n) | Estate1pat(n, _) -> n

    let called_states_of_handler s_trans =
      (* the name defined by the call to a state *)
      let called_states acc escape_list =
	let escape acc { e_next_state } = state_names acc e_next_state in
	List.fold_left escape acc escape_list in
      called_states S.empty s_trans

    (* build the table *)
    let init_table is_weak handlers se_opt =
      let add init_state_names ({ s_state; s_loc; s_trans } as handler) 
            ({ t_initials; t_remaining } as table, handlers_initial,
             handlers_remaining) =
        let state_name = state_patname s_state in
        let e_target_states = called_states_of_handler s_trans in
        let entry =
          { e_loc = s_loc; e_defnames = empty; 
            e_trans_defnames = empty; e_target_states } in
        if S.mem state_name init_state_names then
          { table with t_initials = Env.add state_name entry t_initials },
          handler :: handlers_initial, handlers_remaining
        else 
          { table with t_remaining = Env.add state_name entry t_remaining },
          handlers_initial, handler :: handlers_remaining in
      (* compute the set of initial states *)
      let init_state_names =
        match se_opt with
        | None ->
           (* the first handler gives the initial state *)
           S.singleton (statepat_name_of_handler (List.hd handlers))
        | Some(se) -> state_names S.empty se in                        
      (* initialise the table *)
      let table, handlers_initial, handlers_remaining =
        List.fold_right
          (add init_state_names)
          handlers
          ({ t_initials = Env.empty; t_remaining = Env.empty; t_weak = is_weak },
           [], []) in
      table, handlers_initial, handlers_remaining

    (* sets the [defined_names] for [state_name] *)
    let set_defnames_for_state table defined_names state_name =
      let { e_loc; e_trans_defnames } as entry = find state_name table in
      (* check that names do not appear already in transitions *)
      let _ = add e_loc defined_names e_trans_defnames in
      entry.e_defnames <- defined_names
      
    let set_defnames_for_transition table h defined_names state_name =
      let { e_loc; e_defnames; e_trans_defnames } as entry = find state_name table in
      (* check that names do not appear already in the state *)
      let _ = add e_loc e_defnames e_trans_defnames in
      (* merge names with existing ones in transitions *)
      if not (Defnames.is_empty defined_names) then
        entry.e_trans_defnames <-
          merge e_loc h [defined_names; e_trans_defnames]
                
    (* iterate the previous function for a list of states *)
    let set_defnames_for_transitions table h defined_names state_names =
      S.iter (set_defnames_for_transition table h defined_names) state_names

    (* computes the set of names that are defined *)
    (* and have a last value. It depend on whether transitions are weak *)
    (* ([until]) or strong ([unless]) *)
    let initialized_names_in_initial_states { t_weak; t_initials } loc h =
      if t_weak then
        merge loc h
          (List.map (fun (_, { e_defnames; e_trans_defnames }) ->
               union e_defnames e_trans_defnames)
             (Env.to_list t_initials))
    else empty

    (* given a map [n, entry] compute the set of defined names *)
    (* merge the names defined in every state handler *)
    let check { t_initials; t_remaining } loc h =
      let check n_entry loc h =
        let defnames_list =
          Env.fold (fun _ { e_defnames; e_trans_defnames } acc ->
              union e_defnames e_trans_defnames :: acc) n_entry [] in
        let defined_names = merge loc h defnames_list in
        defined_names in
      let initials_defnames = check t_initials loc h in
      let remaining_defnames = check t_remaining loc h in
      if Env.is_empty t_initials then remaining_defnames
      else if Env.is_empty t_remaining then Defnames.empty
      else merge loc h [initials_defnames; remaining_defnames]
    
    (* check that all states of the automaton are potentially accessible *)
    let check_that_all_states_are_reachable loc
          ({ t_initials; t_remaining } as table) = 
      (* states that are accessible in one hop and not already reached *)
      let next s_set =
        let next s_name acc =
          let { e_target_states } = find s_name table in
          S.union acc e_target_states in
        S.fold next s_set S.empty in

      (* initial states and all states *)
      let init_states = 
        Env.fold (fun n _ acc -> S.add n acc) t_initials S.empty in
      let all_states = 
        Env.fold (fun n _ acc -> S.add n acc) t_remaining init_states in
      let one = ref init_states in
      let reached = ref S.empty in
      
      (* fix point computation *)
      while not (S.is_empty !one) do
        (* add state accessible in one hop from the current states *)
        (* but not already visited (reached) *)
        one := S.diff (next !one) !reached;
        reached := S.union !reached !one
      done;
      let unreachable_states = S.diff all_states !reached in
      if not (S.is_empty unreachable_states)
      then warning loc (Wunreachable_state (S.choose unreachable_states))        
    
    (*
    (* sets the [defined_names] for [state_name] *)
    let add_state { t_initials; t_remaining } defined_names state_name =
      let entry =
        try Env.find state_name t_initials
        with Not_found -> Env.find state_name t_remaining in
      entry.e_state <- defined_names
          
    (* sets the [defined_names] for one transition in [state_name] *)
    let add_transition { t_initials; t_remaining } defined_names
          state_name target_state_name =
      let { e_state; e_trans } as e =
        try Env.find state_name t_initials
        with Not_found -> Env.find state_name t_remaining in
      e.e_trans <- (target_state_name, defined_names) :: e_trans
    
    (* for an [until] transition, the names defined on a transition *)
    (* belong to the source state. Hence, they must be distinct. For an *)
    (* [unless] transition, they belong to the target state. Hence, *)
    (* they must be distinct. *)
    (* In Zelus (w.r.t Lucid Synchrone), all transitions in an automaton *)
    (* are of the same sort ([until or unless]) *)
    let check_state
          { t_weak; t_initials; t_remaining } h
          _ { e_loc; e_state; e_trans } =
      let check (target_name, target_defined_names) =
        let _ = if t_weak then
                  add e_loc e_state target_defined_names
                else
                  let { e_loc; e_state } =
                    try Env.find target_name t_initials
                    with Not_found -> Env.find target_name t_remaining in
                  add e_loc e_state target_defined_names in
        () in
      List.iter check e_trans

    (* computes the set of names that are defined *)
    (* and have a last value. It depend on whether transitions are weak *)
    (* ([until]) or strong ([unless]) *)
    let names_in_initial_states { t_weak; t_initials } loc h =
      if t_weak then empty
      else
        merge loc h (List.map (fun (_, { e_state }) -> e_state)
                       (Env.to_list t_initials))

    (* computes the names defined by an automaton *)
    (* and check that transitions do not redefine names *)
    let check ({ t_initials; t_remaining } as table) loc h =
      Env.iter (check_state table h) t_initials;
      Env.iter (check_state table h) t_remaining;
      let defnames_list =
        Env.fold (fun _ { e_state } acc -> e_state :: acc) t_initials [] in
      let defnames_list =
        Env.fold
          (fun _ { e_state } acc -> e_state :: acc) t_remaining defnames_list in
      let defined_names = merge loc h defnames_list in
      let defined_names_in_transitions =
        Env.fold
          (fun _ { e_trans } acc ->
            List.fold_left (fun acc (_, defnames) -> Defnames.union defnames acc)
              acc e_trans) t_initials empty in
      let defined_names_in_transitions =
        Env.fold
          (fun _ { e_trans } acc ->
            List.fold_left (fun acc (_, defnames) -> Defnames.union defnames acc)
              acc e_trans) t_initials defined_names_in_transitions in
      union defined_names defined_names_in_transitions
             *)    
  end
