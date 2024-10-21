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

(* removing automata in equations *)
open Misc
open Location
open Ident
open Zelus
open Aux
open Mapfold
    
(* Translation of automata. *)
(* Strong transitions: *)
(* automaton
   | S1(p) -> locals in
           do eq_list
           unless | c1 then do eq_list'1 in S'1(e'1) | ...
   | S2(p) -> ...p... | c2 then ...p...
   ...
   init Si(e)
   end

is translated into:

   local state, res in
   do  init state = S1
   and init res = false
   and
   match last state with
   | S1(p) -> reset
             present
             | c'1 -> eq_list'1
                      and state = S'1(e'1) and res = true
             | ...
             else res = false
           every last res
   | S2(p) -> ... p ...
   end
   and
   match state with
   | S1(p) -> reset
              locals in do eq_list
           every res
   | S2(p) -> ...p... *)

(* Weak transitions: *)
(* automaton
   | S1 -> locals in
           do eq_list
           until | c1 then do eq_list'1 in S'1(e'1) | ...
   | S2(p) -> ...p... | c2 then ...
   ...
   end

is translated into:

   local state, res in
   do init state = S1 in
   do init res = false in
   match last state with
   | S1(p) -> reset
              locals
            and
              eq_list
            and
              present
              | c1 -> eq_list1 and
                      state = S'1(e'1) and res = true
              | ...
              else res = false
           every last res
   | S2(p) -> ...last p...
   end

2. Builds a local table table_of_types for every new type

for every automaton, define a type:

type ('a1,...,a'n) state_k = | S1 of 'a1 | ... | Sn of 'an
*)

let fresh_state () = Ident.fresh "state"
let fresh_reset () = Ident.fresh "res"

let eq_present handlers default =
  match handlers with
  | [] -> default
  | _ -> Aux.eq_present handlers (Else(default))

(* introduce a new type for an automaton *)
(* type ('a1,...,'ak) state_k = St1 [of 'a1] | ... | Stm [of 'an] *)
(* depending on the arity of the state handler. This code is taken and *)
(* adapted from the Lucid Synchrone compiler *)
let intro_type_for_automaton acc s_h_list =
  let v i = "a" ^ (string_of_int(i)) in
  (* build the result type *)
  let type_of (i, acc) { s_state = { desc } } =
    match desc with
    | Estate0pat(s1) ->
        (* arity = 0 *)
        make (Econstr0decl(Ident.name s1)), (i, acc)
    | Estate1pat(s1, _) ->
        make (Econstr1decl(Ident.name s1, [make (Etypevar(v i))])),
        (i+1, v i :: acc) in
  let constr_decl_list, (_, a1_ak) =
    Util.mapfold type_of (1, []) s_h_list in
  let ty_decl = make (Evariant_type constr_decl_list) in

  (* introduce a new type *)
  let name = "state__" ^ (string_of_int(Genames.symbol#name)) in
  
  make (Etypedecl { name; ty_params = a1_ak; ty_decl }) ::
  acc

(* Translation of an automaton *)
let automaton acc is_weak handlers state_opt =
  (* introduce a sum type to represent states *)
  let acc = intro_type_for_automaton acc handlers in

  let lname id = Lident.Name(Ident.name id) in
  
  (* translate states *)
  let statepat { desc; loc } =
    let desc =
      match desc with
      | Estate0pat(n) -> Econstr0pat(lname n)
      | Estate1pat(n, l) -> Econstr1pat(lname n, List.map Aux.varpat l) in
    { (Aux.pmake desc) with pat_loc = loc } in
  
  (* translating a state *)
  let rec state { desc; loc } =
    (* make an equation [n = e] *)
    match desc with
    | Estate0(n) ->
       { (Aux.emake (Econstr0 { lname = lname n })) with e_loc = loc }
    | Estate1(n, e_list) ->
       { (Aux.emake (Econstr1 { lname = lname n; arg_list = e_list }))
       with e_loc = loc }
    | Estateif(e, st1, st2) ->
       ifthenelse e (state st1) (state st2) in
  
  (* the name of the initial state *)
  let initial_state =
    match state_opt with
    | None ->
       (* the initial state is the first in the list *)
       let { desc; loc } = (List.hd handlers).s_state in
       begin match desc with
       | Estate0pat(n) ->
          { (Aux.emake (Econstr0 { lname = lname n })) with e_loc = loc }
       | _ -> assert false
       end
    | Some(si) -> state si in
  
  (* [state_name] is the target state computed in the current step *)
  (* [reset_name] is the target reset bit computed in the current step *)
  let state_name = fresh_state () in
  let reset_name = fresh_reset () in

  let state_var n = Aux.var n in
  let reset_var n = Aux.var n in
  let state_last n = Aux.last_star n in
  let reset_last n = Aux.last_star n in

  (* Translation of an escape handler *)
  let escape 
        { e_loc; e_zero; e_cond; e_env; e_reset; e_let; e_body; e_next_state } =
    { p_cond = e_cond; p_env = e_env; p_loc = e_loc; p_zero = e_zero;
      p_body =
        eq_let_list e_let
          (Aux.par [(id_eq state_name (state e_next_state));
                    id_eq reset_name (bool e_reset);
                    eq_local e_body]) } in
  
  (* Translation of strong transitions *)
  let strong { s_state; s_body; s_trans } =
    let pat = statepat s_state in
    (* translate the escape expression *)
    let p_h_list = List.map escape s_trans in
    let handler_to_compute_current_state =
      eq_reset (eq_present p_h_list (id_eq reset_name efalse))
        (reset_last reset_name) in
    let handler_for_current_active_state =
      eq_reset (eq_local s_body) (reset_var reset_name) in
    (pat, handler_to_compute_current_state),
    (pat, handler_for_current_active_state) in
  
  (* This function computes what to do with a automaton with weak transitions *)
  (* a single match/with is generated *)
  let weak { s_state; s_body; s_trans } =
    let pat = statepat s_state in
    let p_h_list = List.map escape s_trans in
    let eq_next_state =
      eq_present p_h_list (id_eq reset_name efalse) in
    let eq = Aux.eq_and eq_next_state (eq_local s_body) in
    pat, eq_reset eq (reset_last reset_name) in
  
  (* the code generated for automata with strong transitions *)
  let strong_automaton handlers =
    let handlers = List.map strong handlers in
    let handler_to_compute_current_state_list,
        handler_for_current_active_state_list = List.split handlers in
    [eq_match true (state_last state_name)
       (List.map
          (fun (m_pat, m_body) ->
            { m_pat; m_body; m_env = Env.empty; m_loc = no_location;
              m_reset = false; m_zero = false })
          handler_to_compute_current_state_list);
     eq_match true (state_var state_name)
       (List.map (fun (m_pat, m_body) ->
            { m_pat; m_body; m_env = Env.empty; m_loc = no_location;
              m_reset = false; m_zero = false })
          handler_for_current_active_state_list)] in
  (* the code for automatama with weak transitions *)
  let weak_automaton handlers =
    let handlers = List.map weak handlers in
    [eq_match true (state_last state_name)
       (List.map
          (fun (m_pat, m_body) ->
            { m_pat; m_body; m_env = Env.empty; m_loc = no_location;
              m_reset = false; m_zero = false }) handlers)] in
  (* translate the automaton *)
  let eq_list =
    if is_weak then weak_automaton handlers else strong_automaton handlers in
  (* initial state and reset value *)
  Aux.eq_local_vardec
    [Aux.init_vardec state_name false None None true;
     Aux.init_vardec reset_name false None None true]
    (eq_init state_name initial_state ::
         eq_init reset_name efalse :: eq_list), acc

(* Translation of equations *)
let equation funs acc eq =
  let eq, acc = Mapfold.equation funs acc eq in
  match eq.eq_desc with
  | EQautomaton { is_weak; handlers; state_opt } ->
     automaton acc is_weak handlers state_opt
  | _ -> raise Mapfold.Fallback
         
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; set_index; get_index; global_funs } in
  let { p_impl_list } as p, acc = Mapfold.program_it funs [] p in
  { p with p_impl_list = acc @ p_impl_list }
