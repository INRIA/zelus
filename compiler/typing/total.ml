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
let empty = { dv = S.empty; di = S.empty; dr = S.empty }

(* add two sets of names provided they are distinct *)
let add loc { dv = dv1; di = di1; dr = dr1 } { dv = dv2; di = di2; dr = dr2 } =
  let add set1 set2 =
    S.fold 
      (fun elt set -> 
	if not (S.mem elt set) then S.add elt set
	else error loc (Ealready(elt))) set1 set2 in
  { dv = add dv1 dv2; di = add di1 di2; dr = add dr1 dr2 }

(* checks that every partial name defined at this level *)
(* has a last value *)
let all_last loc h set =
  let check elt =
    try
      let ({ t_sort = k; t_typ = ty } as tentry) = Env.find elt h in
      match k with
          | Mem ({ t_default = Previous; t_next_is_set = next } as m) ->
	    (* When [m] is not defined in a branch *)
	    (* this one is implicitely complemented with [next m = m] *)
	    (* if the next value of [m] is defined and with [m = last m] *)
	    if not next then
	      tentry.t_sort <- Mem { m with t_last_is_used = true }
        | Mem { t_default = Absent } | Val -> 
            begin try ignore (Types.filter_signal ty)
              with Types.Unify -> error loc (Eshould_be_a_signal(elt))
            end
	| Mem { t_default = Default } | ValDefault _ -> ()
    with
      | Not_found -> () in
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
  let split (acc_dv, acc_di, acc_dr) { dv = dv; di = di; dr = dr } =
    dv :: acc_dv, di :: acc_di, dr :: acc_dr in
  let dv, di, dr = List.fold_left split ([], [], []) defnames_list in
  let dv_total, dv_partial = merge dv in
  let di_total, di_partial = merge di in
  let dr_total, dr_partial = merge dr in
  (dv_total, dv_partial), (di_total, di_partial), (dr_total, dr_partial)

(* The main entry. Identify variables which are partially defined *)
let merge loc h defnames_list =
  let
      (dv_total, dv_partial), (di_total, di_partial), (dr_total, dr_partial) =
    merge_defnames_list defnames_list in
  (* every partial variable must be defined as a memory *)
  all_last loc h (S.diff dv_partial di_total);
  (* for initialized values, all branches must give a definition *)
  if not (S.is_empty di_partial) 
  then error loc (Einit_undefined(S.choose(di_partial)));
  (* the default equation for a derivative is [der x = 0] so nothing *)
  (* has to be done *)
  add loc { dv = dv_partial; di = di_partial; dr = dr_partial }
    { dv = dv_total; di = di_total; dr = dr_total }

(* Join two sets of names in a parallel composition. Check that names *)
(* are only defined once. Moreover, reject [der x = ...] and [x = ...] *)
let join loc { dv = dv1; di = di1; dr = dr1 } { dv = dv2; di = di2; dr = dr2 } =
  let join names1 names2 =
    let joinrec n acc = 
      if S.mem n names1 then error loc (Edefined_twice(n)) else S.add n acc in
    S.fold joinrec names2 names1 in
  let disjoint names1 names2 =
    let disjointrec n = 
      if S.mem n names1 then error loc (Edefined_twice(n)) in
    S.iter disjointrec names2 in
  disjoint dv1 dr2;
  disjoint dv2 dr1;
  { dv = join dv1 dv2; di = join di1 di2; dr = join dr1 dr2 }
  
(* check that every initialized name [init x = ...] comes with *)
(* a definition of [x = ...]. This is not a bug but a warning is produced *)
let initialization_with_definition loc n { t_sort = sort } =
  match sort with
    | Val | ValDefault _ | Mem { t_initialized = false } -> ()
    | Mem { t_initialized = true; t_der_is_defined = der;
	    t_is_set = set; t_next_is_set = next } ->
        if not (set || next || der) then
	  Format.eprintf 
	    "%aWarning: the variable %s is initialized \
               but no definition is given.@."
            output_location loc
	    (Ident.source n)

let check_initialization_associated_to_a_definition_env loc h =
  Env.iter (initialization_with_definition loc) h

let check_initialization_associated_to_a_definition_names loc h n_list =
  List.iter 
    (fun n -> let entry = try Env.find n h with Not_found -> assert false in
	      initialization_with_definition loc n entry)
    n_list

(** Check totality of automata *)
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
      let add acc { s_state = statepat; s_body = { b_loc = loc } } =
        Env.add (statepatname statepat)
          { e_loc = loc;
            e_state = empty;
            e_until = empty;
            e_unless = empty } acc in
      let { s_state = statepat; s_body = { b_loc = loc } } = 
	List.hd state_handlers in
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
      add loc defined_names_in_states defined_names_in_transitions
  end
