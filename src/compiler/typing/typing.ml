(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2023 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* type checking *)
(* must be done after write variables have been computed *)
(* and equations annotated *)

(* H  |-{expected_k}{actual_k} e : t  and H |-{expected_k}{actual_k} eq | W *)
(* H : typing environment           *)
(* expected_k : the expected kind   *)
(* actual_k : the actual kind <= expected_k *)
(* e : expression with type t       *)
(* W : defined names *)
(* input: e, expected_k - output: t, actual_k, W *)

open Ident
open Global
open Modules
open Zelus
open Defnames
open Deftypes
open Types
open Typerrors

module Write = Write.Make(Typinfo)

(* environments are extended with a path of kinds. *)
(* entry [k1 on ... ) on kn x: t] means that x was introduced *)
(* in a block with kind [k1] and used in a nested block with *)
(* kinds [k2], ..., [kn]; [kn] being the kind of the block where [x] is used *)
module Env =
  struct
    include Ident.Env
    let on env k =
      map (fun ({ t_path } as entry) -> { entry with t_path = Pon(t_path, k) })
        env
  end

(* accesses in symbol tables for global identifiers *)
let find_value loc f =
  try find_value f
  with Not_found -> error loc (Eglobal_undefined(Value, f))
let find_type loc f =
  try find_type f
  with Not_found -> error loc (Eglobal_undefined(Type, f))
let find_constr loc c =
  try find_constr c
  with Not_found -> error loc (Eglobal_undefined(Constr, c))
let find_label loc l =
  try find_label l
  with Not_found -> error loc (Eglobal_undefined(Label, l))


(** The main unification functions **)
let unify loc expected_ty actual_ty =
  try
    Types.unify expected_ty actual_ty
  with
    | Types.Unify -> error loc (Etype_clash(actual_ty, expected_ty))

let unify_expr expr expected_ty actual_ty =
  try
    Types.unify expected_ty actual_ty
  with
    | Types.Unify -> error expr.e_loc (Etype_clash(actual_ty, expected_ty))

let unify_pat pat expected_ty actual_ty =
  try
    Types.unify expected_ty actual_ty
  with
    | Types.Unify -> error pat.pat_loc (Etype_clash(actual_ty, expected_ty))

let less_than loc actual_k expected_k =
  if not (Kind.is_less_than actual_k expected_k)
  then error loc (Ekind_clash(actual_k, expected_k))

let stateful loc expected_k =
  if not (Kind.stateful expected_k)
  then error loc
         (Ekind_clash(Deftypes.Tnode(Deftypes.Tdiscrete), expected_k))

(* check that a type belong to a kind *)
let check_type_is_in_kind loc h vkind =
  let type_in_kind loc ty actual_k =
    if not (Kind.in_kind vkind ty)
    then error loc (Etype_kind_clash(actual_k, ty)) in
  Env.iter (fun _ { t_tys = { typ_body } } ->
      type_in_kind loc typ_body vkind) h

(* Check that no size variables are all bounded *)
let check_no_unbounded_size_name loc h =
  let check_no_unbounded_size_name loc fv ty =
    if not (S.is_empty fv)
    then let n = S.choose fv in
         error loc (Esize_parameter_cannot_be_generalized(n, ty)) in
  Env.iter
    (fun _ { t_tys = { typ_body } } ->
      check_no_unbounded_size_name loc (Types.fv S.empty typ_body) typ_body) h
 
let less_than loc actual_k expected_k =
  if not (Kind.is_less_than actual_k expected_k)
  then error loc (Ekind_clash(actual_k, expected_k))

(* kind from a path [kind_of_path(k1 on ... on kn) = k1] *)
(* check that k1 <= k{i+1} *)
let kind_of_path loc path =
  let rec kind path = match path with
    | Pkind(k) -> k
    | Pon(path, k_on) ->
     let k = kind path in
     less_than loc k k_on;
     k in
  kind path

(* returns the sort of the function value (either constant or static) *)
(* and that of the body of the function *)
let kind_of_funexp loc expected_k arg_v expected_body_k =
  let expected_body_k =
    match arg_v, expected_body_k with
    | _, Tfun(v) -> Tfun(arg_v)
    | Tany, Tnode _ -> expected_body_k
    | _ -> error loc (Ekind_clash(expected_k, Tfun(arg_v))) in
  let actual_k =
    match expected_k, arg_v, expected_body_k with
    | _, Tconst, _ -> Tfun(Tconst)
    | Tfun(Tconst), Tstatic, _ -> Tfun(Tconst)
    | Tfun(Tstatic), _, _ -> Tfun(Tstatic)
    | _, Tstatic, _ -> Tfun(Tstatic)
    | Tfun(Tany), Tany, Tfun _ -> Tfun(Tany)
    | _ , Tany, Tnode _ -> Tfun(Tstatic)
    | _, Tany, _ -> Tfun(Tany) in
  actual_k, expected_body_k
           
(* An equation is expansive if one is *)
let rec expansive { eq_desc } =
  (* an expression is expansive if it is an application *)
  let rec exp { e_desc } =
    match e_desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Efun _ -> false
    | Etuple(e_list) -> List.exists exp e_list
    | Erecord(l_e_list) -> List.exists (fun { arg } -> exp arg) l_e_list
    | Erecord_access { arg } | Etypeconstraint(arg, _) -> exp arg
    | Erecord_with(e, l_e_list) ->
       exp e || List.exists (fun { arg } -> exp arg) l_e_list
    | _ -> true in
  match eq_desc with
  | EQeq(_, e) -> exp e
  | EQand { eq_list } -> List.exists expansive eq_list
  | _ -> true
       
(* The type of states in automata **)
(* We emit a warning when a state is entered both by reset and history *)
type state = { mutable s_reset: bool option; s_parameters: typ list }

let check_target_state loc expected_reset actual_reset =
  match expected_reset with
  | None -> Some(actual_reset)
  | Some(expected_reset) ->
     if expected_reset <> actual_reset then
       warning loc (Wreset_target_state(actual_reset, expected_reset));
     Some(expected_reset)

(** Typing immediate values *)
let immediate = function
  | Ebool _ -> Initial.typ_bool
  | Eint(i) -> Initial.typ_int
  | Efloat(i) -> Initial.typ_float
  | Echar(c) -> Initial.typ_char
  | Estring(c) -> Initial.typ_string
  | Evoid -> Initial.typ_unit

(* Types for local identifiers *)
let var loc h n =
  try Env.find n h with | Not_found -> error loc (Evar_undefined(n))

let typ_of_var loc h n = let { t_tys } = var loc h n in t_tys

(* Typing [last n] *)
let last loc h n =
  let { t_path; t_sort; t_tys } as entry = var loc h n in
  (* [last n] is allowed only if [n] is declared in a stateful block *)
  let actual_k = kind_of_path loc t_path in
  let t_sort =
    match actual_k with
    | Tnode _ -> Deftypes.last t_sort
    | Tfun _ -> error loc (Elast_forbidden(n)) in
  entry.t_sort <- t_sort;
  Types.instance t_tys

(* Typing [der n = ...] *)
let derivative loc h n =
  let { t_path; t_sort; t_tys } as entry = var loc h n in
  let _ = kind_of_path loc t_path in
  entry.t_sort <- Deftypes.cont t_sort;
  Types.instance t_tys

(* Typing [init n = ...] *)
let init loc h n =
  (* set that [n] is initialized if it is not already at the definition point *)
  let { t_path; t_sort; t_tys } as entry = var loc h n in
  let _ = kind_of_path loc t_path in
  let t_sort =
    match t_sort with
    | Sort_mem { m_init = Decl _ } ->
       (* it is already initialized at declaration point *)
       error loc (Ealready(Initial, n))
    | _ -> Deftypes.init t_sort in
  entry.t_sort <- t_sort;
  Types.instance t_tys

(* Typing [n = ...] *)
let def loc h n =
  let { t_tys } as entry = var loc h n in
  Types.instance t_tys

(** Types for global identifiers *)
let global loc lname =
  let { qualid; info = { value_typ = tys } } = find_value loc lname in
  qualid, Types.instance tys

let global_with_instance loc lname =
  let { qualid; info = { value_const; value_typ = tys } } =
    find_value loc lname in
  let typ_instance, typ_body = Types.instance_and_vars_of_type tys in
  qualid, value_const, typ_instance, typ_body

let get_label loc l =
  let { qualid = qualid; info = tys_label } = find_label loc l in
  qualid, Types.label_instance tys_label

let get_constr loc c =
  let { qualid = qualid; info = tys_c } = find_constr loc c in
  qualid, Types.constr_instance tys_c

let rec get_all_labels loc ty =
  match ty.t_desc with
  | Tconstr(qual, _, _) ->
     let { info = { type_desc = ty_c } } =
       find_type loc (Lident.Modname(qual)) in
     begin match ty_c with
             Record_type(l) -> l
           | _ -> assert false
     end
  | Tlink(link) -> get_all_labels loc link
  | _ -> assert false

(** Check that every declared name is associated to a defining equation *)
(* Returns a new [defined_names] where names from [n_list] *)
(* have been removed *)
let check_definitions_for_every_name defined_names n_list =
  List.fold_left
    (fun { dv; di; der }
         { var_name = n; var_loc = loc; var_default; var_init } ->
     let in_dv = S.mem n dv in
     let in_di = S.mem n di in
     let in_der = S.mem n der in
      (* check that n is defined by an equation *)
     if not (in_dv || in_di || in_der)
     then error loc (Eequation_is_missing(n));
     (* check that [n] has a single def. for its initial value *)
     if in_di && not (var_init = None)
     then error loc (Ealready(Initial, n));
     (* remove local names *)
     { dv = if in_dv then S.remove n dv else dv;
       di = if in_di then S.remove n di else di;
       der = if in_der then S.remove n der else der })
    defined_names n_list

(* Computes the type from a vardec list *)
let type_of_vardec_list n_list =
  let type_of_vardec { var_info } = Typinfo.get_type var_info in
  let ty_list = List.map type_of_vardec n_list in
  match ty_list with
  | [] -> Initial.typ_unit
  | [ty] -> ty
  | _ -> Types.product ty_list
    
(* make a function type from a function definition. *)
(* remove useless dependences:
 * - (n:ty_arg) -k-> ty_res => ty_arg -k-> ty_res if n not in fv_size(ty_res) *)
let arrowtype loc expected_k name_ty_list ty_res =
  let rec arg name_ty_list fv =
    match name_ty_list with
    | [] -> [], fv
    | (n_opt, ty) :: name_ty_list ->
       let p_ty_list, fv = arg name_ty_list fv in
       match n_opt with
       | None -> (None, ty) :: p_ty_list, fv
       | Some(n) ->
          let n_opt, fv = if S.mem n fv then n_opt, S.remove n fv
                          else None, fv in
          let fv = Types.fv fv ty in
          (n_opt, ty) :: p_ty_list, fv in
  let name_ty_list, fv = arg name_ty_list (Types.fv S.empty ty_res) in
  Types.arrowtype_list expected_k name_ty_list ty_res

let entry k sort = Deftypes.entry k sort (Deftypes.scheme (Types.new_var ()))
 
let env_of_pattern expected_k acc pat =
  let entry x acc = Env.add x (entry expected_k Sort_val) acc in
  let rec pattern acc { pat_desc } =
    match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> acc
    | Econstr1pat(_, pat_list) | Etuplepat(pat_list) ->
       pattern_list acc pat_list
    | Evarpat(x) -> entry x acc
    | Etypeconstraintpat(p, _) | Eorpat(p,_) -> pattern acc p
    | Ealiaspat(p, x) ->
       let acc = pattern acc p in
       entry x acc
    | Erecordpat(label_pat_list) ->
       List.fold_left (fun acc { arg } -> pattern acc arg) acc label_pat_list
  and pattern_list acc p_list = List.fold_left pattern acc p_list in
  pattern acc pat

let env_of_scondpat expected_k scpat =
  let rec env_of acc { desc } =
    match desc with
    | Econdand(sc1, sc2) -> env_of (env_of acc sc1) sc2
    | Econdor(sc, _) | Econdon(sc, _) -> env_of acc sc
    | Econdexp _ -> acc
    | Econdpat(_, pat) -> env_of_pattern expected_k acc pat in
  env_of Env.empty scpat
 
and env_of_statepat expected_k spat =
  let env_of acc { desc } =
    match desc with
    | Estate0pat _ -> acc
    | Estate1pat(_, l) -> List.fold_left (fun acc n -> S.add n acc) acc l in
  let acc = env_of S.empty spat in
  S.fold (fun n acc -> Env.add n (entry expected_k Sort_val) acc) acc Env.empty

let env_of_pattern expected_k pat = env_of_pattern expected_k Env.empty pat  

(* for every entry [x, tentry] in [env], add the tag [InitEq] if [x in di] *)
let add_init_eq_of_env env { di } =
  Env.mapi
    (fun n ({ t_sort } as entry) ->
      if S.mem n di then { entry with t_sort = Deftypes.init t_sort }
      else entry)
    env

(* introduce an entry for name [n] according to [expected_k] *)
let intro_sort expected_k =
  match expected_k with
  | Tfun _ -> Sort_val
  | Tnode _ -> Sort_mem Deftypes.empty_mem
    
(* introduce a typing environment from a set of names *)
let env_of_equation expected_k { eq_write } =
  let n_set = Defnames.names S.empty eq_write in
  let env =
    S.fold
      (fun n acc -> Env.add n (entry expected_k (intro_sort expected_k)) acc)
      n_set Env.empty in
  add_init_eq_of_env env eq_write

(** Typing a pateq **)
let pateq h { desc; loc } ty_e =
  let n = List.length desc in
  let ty_e_list =
    try
      Types.filter_product (List.length desc) ty_e with | Unify -> [ty_e] in
  try
    List.fold_left2
      (fun acc x expected_ty ->
        unify loc expected_ty (def loc h x); S.add x acc)
      S.empty desc ty_e_list
  with
  | _ -> error loc (Earity_clash(n, List.length ty_e_list))
       
(* Typing a size expression *)
let rec size h expected_k { desc; loc } =
  match desc with
  | Size_int(i) -> Types.size_int i
  | Size_var(x) ->
      let { t_tys; t_path } = var loc h x in
      let t_typ = Types.instance t_tys in
      unify loc Initial.typ_int t_typ;
      let actual_k = kind_of_path loc t_path in
      less_than loc actual_k expected_k;
      Types.size_var x
  | Size_op(op, s1, s2) ->
     let op = match op with
       | Size_plus -> Splus | Size_minus -> Sminus | Size_mult -> Smult in
     let s1 = size h expected_k s1 in
     let s2 = size h expected_k s2 in
     Types.size_op op s1 s2
  | Size_frac { num; denom } ->
      let num = size h expected_k num in
      Types.size_frac num denom

(* Convert an expression into a size expression *)
let rec size_of_exp { e_desc; e_loc } =
  match e_desc with
  | Econst(Eint(i)) -> Types.size_int i
  | Evar(n) -> Types.size_var n
  | Eapp { f = { e_desc = Eglobal { lname = Lident.Modname(qualid) } };
           arg_list = [e1; e2] } ->
     let s1 = size_of_exp e1 in
     let s2 = size_of_exp e2 in
     if qualid = Initial.stdlib_name "+"
     then Types.size_op Splus s1 s2
     else if qualid = Initial.stdlib_name "-"
     then Types.size_op Sminus s1 s2
     else if qualid = Initial.stdlib_name "*"
     then Types.size_op Smult s1 s2
     else if qualid = Initial.stdlib_name "/"
     then match e2.e_desc with
          | Econst(Eint(i)) -> Types.size_frac s1 i
          | _ -> error e_loc Enot_a_size_expression
     else error e_loc Enot_a_size_expression
  | _ -> error e_loc Enot_a_size_expression

(** Typing patterns **)
(* the kind of variables in [p] must be equal to [expected_k] *)
let rec pattern h ({ pat_desc; pat_loc; pat_info } as pat) ty =
  (* type annotation *)
  pat.pat_info <- Typinfo.set_type pat_info ty;
  match pat_desc with
  | Ewildpat -> ()
  | Econstpat(im) ->
     unify_pat pat ty (immediate im);
  | Econstr0pat(c0) ->
     let qualid, { constr_res = ty_res; constr_arity = n } =
       get_constr pat_loc c0 in
     (* check the arity *)
     if n <> 0 then error pat_loc (Econstr_arity(c0, n, 0));
     unify_pat pat ty ty_res;
     pat.pat_desc <- Econstr0pat(Lident.Modname(qualid));
  | Econstr1pat(c1, pat_list) ->
     let qualid,
         { constr_arg = ty_list; constr_res = ty_res; constr_arity = n } =
       get_constr pat_loc c1 in
     (* check the arity *)
     let actual_n = List.length pat_list in
     if n <> actual_n then error pat_loc (Econstr_arity(c1, n, actual_n));
     unify_pat pat ty ty_res;
     pat.pat_desc <- Econstr1pat(Lident.Modname(qualid), pat_list);
     List.iter2 (pattern h) pat_list ty_list
  | Evarpat(x) ->
     let actual_ty = Types.instance (typ_of_var pat_loc h x) in
     unify_pat pat ty actual_ty
  | Etuplepat(pat_list) ->
     let ty_list = List.map (fun _ -> new_var ()) pat_list in
     unify_pat pat ty (product ty_list);
     List.iter2 (pattern h) pat_list ty_list
  | Etypeconstraintpat(p, typ_expr) ->
     let expected_typ =
       Types.instance (Interface.scheme_of_type typ_expr) in
     unify_pat pat expected_typ ty;
     pattern h p ty
  | Erecordpat(label_pat_list) ->
     let label_pat_list =
       List.map
         (fun { label; arg } ->
          let qualid, { label_arg = ty_arg; label_res = ty_res } =
            get_label pat.pat_loc label in
          unify_pat arg ty ty_arg;
          pattern h arg ty_res;
          { label = Lident.Modname(qualid); arg = arg }) label_pat_list in
     pat.pat_desc <- Erecordpat(label_pat_list)
  | Ealiaspat(p, x) ->
     let actual_ty = Types.instance (typ_of_var pat_loc h x) in
     unify_pat pat ty actual_ty;
     pattern h p ty
  | Eorpat(p1, p2) ->
     pattern h p1 ty;
     pattern h p2 ty

(* typing a list of patterns. *)
let pattern_list h pat_list ty_list = List.iter2 (pattern h) pat_list ty_list

(* check that a pattern is total *)
let check_total_pattern p =
  let is_exhaustive = Patternsig.check_activate p.pat_loc p in
  if not is_exhaustive then error p.pat_loc Epattern_not_total

let check_total_pattern_list p_list = List.iter check_total_pattern p_list

(** Typing a pattern matching. Returns defined names **)
let match_handlers body loc expected_k h is_total m_handlers pat_ty ty_res =
  let handler ({ m_pat = pat; m_body = b } as mh) =
    let h0 = env_of_pattern expected_k pat in
    pattern h0 pat pat_ty;
    mh.m_env <- h0;
    let h = Env.append h0 h in
    let defined_names, actual_k = body expected_k h b ty_res in
    defined_names, actual_k in
  let defined_names_k_list = List.map handler m_handlers in
  let defined_names_list, k_list = List.split defined_names_k_list in

  (* check partiality/redundancy of the pattern matching *)

  let is_total =
    is_total || (Patternsig.check_match_handlers loc m_handlers) in

  let defined_names_list =
    if is_total then defined_names_list
    else Defnames.empty :: defined_names_list in
  (* identify variables which are defined partially *)
  is_total,
  Total.merge loc h defined_names_list,
  (* the kind is the sup of all kinds *)
  Kind.sup_list k_list

(** Typing a present handler. *)
(*- Returns defined names and the kind is the supremum *)
let present_handlers scondpat body loc expected_k h h_list opt ty_res =
  let handler ({ p_cond; p_body } as ph) =
    (* local variables from [scpat] cannot be accessed through a last *)
    let h0 = env_of_scondpat expected_k p_cond in
    let h = Env.append h0 h in
    let actual_k_spat = scondpat expected_k Initial.typ_bool h p_cond in
    ph.p_env <- h0;
    let defined_names, actual_k = body expected_k h p_body ty_res in
    defined_names, Kind.sup actual_k_spat actual_k in

  let defined_names_k_list = List.map handler h_list in
  let defined_names_list, k_list = List.split defined_names_k_list in

  (* treat the optional default case *)
  let defined_names_list, actual_k =
    match opt with
    | NoDefault -> Defnames.empty :: defined_names_list, Tfun(Tconst)
    | Init(b) ->
       let defined_names, actual_k = body (Tnode(Tdiscrete)) h b ty_res in
       stateful loc expected_k;
       defined_names :: defined_names_list, actual_k
    | Else(b) ->
       let defined_names, actual_k = body expected_k h b ty_res in
       defined_names :: defined_names_list, actual_k in
                          
  (* identify variables which are defined partially *)
  Total.merge loc h defined_names_list,
  Kind.sup actual_k (Kind.sup_list k_list)

(* Every variable defined in the initial states of an automaton *)
(* do have a last value in the remaining ones provided the transition is weak *)
let vars_with_last h { dv = dv } =
  let add n acc =
    let ({ t_sort } as tentry) = Env.find n h in
    match t_sort with
    | Sort_mem ({ m_init = No } as m) ->
       Env.add n { tentry with t_sort = Sort_mem { m with m_init = Eq } } acc
    | Sort_mem _ | Sort_val | Sort_var -> acc in
  let first_h = S.fold add dv Env.empty in
  first_h, Env.append first_h h

(** Typing an automaton. Returns defined names **)
let rec automaton_handlers
          scondpat leqs body body_escape state_expression
          is_weak loc (expected_k: Deftypes.kind) h handlers se_opt =

  (* check that all declared states are accessible; returns the set of *)
  (* initial states *)
  let init_state_names =
    Total.Automaton.check_all_states_are_accessible loc handlers se_opt in
    
  (* global table which associate the set of defined_names for every state *)
  let table = Total.Automaton.init_table is_weak init_state_names handlers in

  (* build the environment of states. *)
  let addname acc { s_state = statepat } =
    match statepat.desc with
      | Estate0pat(s) -> Env.add s { s_reset = None; s_parameters = [] } acc
      | Estate1pat(s, l) ->
          Env.add s { s_reset = None;
                      s_parameters = (List.map (fun _ -> new_var ()) l)} acc in
  let env_of_states = List.fold_left addname Env.empty handlers in

  (* in case [se_opt = None], checks that the initial state is a non *)
  (* parameterised state. *)
  let { s_state = s_first_statepat } = List.hd handlers in
  let actual_k_init =
    match se_opt with
    | None ->
       begin match s_first_statepat.desc with
       | Estate1pat _ -> error s_first_statepat.loc Estate_initial
       | Estate0pat _ -> Tfun(Tconst)
       end
    | Some(se) -> state_expression h env_of_states true se in
  
  (* the type for conditions on transitions *)
  let type_of_condition = Initial.typ_bool in

  (* typing the body of the automaton *)
  let typing_handler h ({ s_state; s_let; s_body; s_trans } as s) =
    let escape source_state h expected_k
        ({ e_cond; e_reset; e_let; e_body; e_next_state } as esc) =
      (* type one escape condition *)
      let h0 = env_of_scondpat expected_k e_cond in
      let h = Env.append h0 h in
      let actual_k_e_cond = scondpat expected_k type_of_condition h e_cond in
      esc.e_env <- h0;
      (* type check the sequence of local equations *)
      let h, actual_k_let = leqs expected_k h e_let in
      (* type check the body *)
      let h, defined_names, actual_k_body =
        body_escape expected_k h e_body in
      (* checks that [state] belond to the current set of [states] *)
      let actual_k_state = state_expression h env_of_states e_reset e_next_state in
      (* checks that names are not defined twice in a state *)
      let state_names =
        if is_weak then S.singleton source_state
        else Total.Automaton.state_names e_next_state in
      Total.Automaton.add_transitions table h defined_names state_names;
      Kind.sup actual_k_e_cond
        (Kind.sup actual_k_let (Kind.sup actual_k_body actual_k_state)) in

    (* typing the state pattern *)
    let h0 = env_of_statepat expected_k s_state in
    s.s_env <- h0;
    begin match s_state.desc with
    | Estate0pat _ -> ()
    | Estate1pat(s, n_list) ->
       let { s_parameters = ty_list } = Env.find s env_of_states in
       List.iter2
         (fun n ty ->
           unify s_state.loc
             (Types.instance (typ_of_var s_state.loc h0 n)) ty) n_list ty_list;
    end;
    let h = Env.append h0 h in
    (* type check the sequence of local equations *)
    let h, actual_k_let = leqs expected_k h s_let in
    (* typing the body *)
    let new_h, defined_names, actual_k_body =
      body expected_k h s_body in
    (* add the list of defined_names to the current state *)
    let s_name = Total.Automaton.state_patname s_state in
    Total.Automaton.add_state table defined_names s_name;
    let actual_k_list =
      List.map (escape s_name new_h expected_k) s_trans in
    let actual_k =
      Kind.sup (Kind.sup_list actual_k_list)
        (Kind.sup actual_k_let actual_k_init) in

    defined_names, actual_k in

  let defined_names_k_list = List.map (typing_handler h) handlers in
  let defined_names_list, k_list = List.split defined_names_k_list in

  (* identify variables which are partially defined in some states *)
  (* and/or transitions *)
  let defined_names = Total.Automaton.check table loc h in
  (* write defined_names in every handler *)
  List.iter2
    (fun { s_body = { b_write = _ } as b } defined_names ->
      b.b_write <- defined_names)
    handlers defined_names_list;

  (* finally, indicate for every state handler if it is entered *)
  (* by reset or not *)
  mark_reset_state env_of_states handlers;
  let actual_k = Kind.sup_list k_list in
  defined_names, Kind.sup actual_k_init actual_k

(* Once the body of an automaton has been typed, indicate for every *)
(* handler if it is always entered by reset or not *)
and mark_reset_state def_states handlers =
  let mark ({ s_state } as handler) =
    let { s_reset = r } =
      Env.find (Total.Automaton.state_patname s_state) def_states in
    let v = match r with | None | Some(false) -> false | Some(true) -> true in
    handler.Zelus.s_reset <- v in
  List.iter mark handlers


(* Typing the declaration of variables. The result is a typing environment *)
(* for names defined and a sort *)
let rec vardec_list expected_k h v_list =
  (* makes an entry *)
  let decl m_opt =
    match m_opt with
    | None -> No
    | Some({ e_desc = Econst(i) }) -> Decl(Some(i)) | _ -> Decl(None) in
  let intro expected_k var_init var_default =
    match expected_k with
    | Tfun _ -> Sort_val
    | Tnode _ ->
       let m_init = decl var_init in
       let m_default = decl var_default in
       Sort_mem { Deftypes.empty_mem with m_init; m_default } in    
  (* typing every declaration *)
  let vardec (acc_h, acc_k)
        ({ var_name; var_default; var_init; var_clock;
          var_typeconstraint; var_loc } as v) =
    let expected_ty = Types.new_var () in
    let h = Env.append acc_h h in
    let actual_k =
      Util.optional_with_default
        (fun e -> expect expected_k h e expected_ty)
        (Tfun(Tconst)) var_default in
    (* the initialization must appear in a statefull function *)
    let actual_k_init =
      Util.optional_with_default
        (fun e -> stateful e.e_loc expected_k;
                  expect (Tnode(Tdiscrete)) h e expected_ty)
        (Tfun(Tconst)) var_init in
    let actual_k = Kind.sup actual_k actual_k_init in
    let t_sort = intro expected_k var_init var_default in
    let entry =
      Deftypes.entry expected_k t_sort (Deftypes.scheme expected_ty) in
    (* type annotation *)
    v.var_info <- Typinfo.set_type v.var_info expected_ty;
    Env.add var_name entry acc_h,
    Kind.sup actual_k (Kind.sup actual_k_init acc_k) in
  List.fold_left vardec (Env.empty, Tfun(Tconst)) v_list

(* [expression expected_k h e] returns the type for [e] and [actual kind] *)
and expression expected_k h ({ e_desc; e_loc } as e) =
  let ty, actual_k = match e_desc with
    | Econst(i) -> immediate i, Tfun(Tconst)
    | Evar(x) ->
       let { t_tys; t_sort; t_path } = var e_loc h x in
       (* H, [k1 on ... on kn x :t ] |- expected_k : t *)
       (* if k1 <= expected_k /\ k1 <= ki *)
       let actual_k = kind_of_path e_loc t_path in
       less_than e_loc actual_k expected_k;
       let ty = Types.instance t_tys in
       ty, actual_k
    | Eglobal ({ lname = lname } as g) ->
       let qualid, is_const, typ_instance, ty =
         global_with_instance e_loc lname in
       g.lname <- Lident.Modname(qualid);
       (**** g.typ_instance <- typ_instance; *)
       let actual_k = Tfun(if is_const then Tconst else Tstatic) in
       less_than e_loc actual_k expected_k;
       ty, actual_k
    | Elast { id } -> last e_loc h id, Tfun(Tany)
    | Etuple(e_list) ->
       let ty_k_list = List.map (expression expected_k h) e_list in
       let ty_list, k_list = List.split ty_k_list in
       product ty_list, Kind.sup_list k_list
    | Eop(op, e_list) ->
       operator expected_k h e_loc op e_list
    | Eapp { f; arg_list } ->
       apply e_loc expected_k h f arg_list
    | Econstr0({ lname } as c) ->
       let qualid, { constr_res = ty_res; constr_arity = n } =
         get_constr e_loc lname in
       if n <> 0 then error e_loc (Econstr_arity(lname, n, 0));
       c.lname <- Lident.Modname(qualid);
       ty_res, Tfun(Tconst)
    | Econstr1({ lname; arg_list } as c) ->
       let qualid,
           { constr_arg = ty_list; constr_res = ty_res; constr_arity = n } =
         get_constr e_loc lname in
       let actual_arity = List.length arg_list in
       if n <> actual_arity then
         error e_loc (Econstr_arity(lname, n, actual_arity));
       let actual_k_list = List.map2 (expect expected_k h) arg_list ty_list in
       c.lname <- Lident.Modname(qualid);
       ty_res, Kind.sup_list actual_k_list
    | Erecord_access({ label; arg } as r) ->
       let qualid, { label_arg = ty_arg; label_res = ty_res } =
         get_label e_loc label in
       let actual_k = expect expected_k h arg ty_arg in
       r.label <- Lident.Modname(qualid);
       ty_res, actual_k
    | Erecord(label_e_list) ->
       let ty = new_var () in
       let actual_k_list =
         List.map (type_label_arg expected_k ty h e_loc) label_e_list in
       (* check that no field is missing *)
       let label_desc_list = get_all_labels e_loc ty in
       if List.length label_e_list <> List.length label_desc_list
       then error e_loc Esome_labels_are_missing;
       ty, Kind.sup_list actual_k_list
    | Erecord_with(e1, label_e_list) ->
       let ty = new_var () in
       let actual_k_list =
         List.map (type_label_arg expected_k ty h e_loc) label_e_list in
       let actual_k = expect expected_k h e1 ty in
       ty, Kind.sup actual_k (Kind.sup_list actual_k_list)
    | Etypeconstraint(exp, typ_expr) ->
       let expected_typ =
         Types.instance (Interface.scheme_of_type typ_expr) in
       let actual_k = expect expected_k h exp expected_typ in
       expected_typ, actual_k
    | Elet(l, e) ->
       let h, actual_k = leq expected_k h l in
       let ty, actual_k_e = expression expected_k h e in
       ty, Kind.sup actual_k actual_k_e
    | Efun(fe) ->
       let ty, actual_k = funexp expected_k h fe in
       ty, actual_k
    | Ematch({ is_total; e; handlers } as mh) ->
        let expected_pat_ty, actual_pat_k = expression expected_k h e in
        let expected_ty = new_var () in
        let is_total, actual_k_h =
          match_handler_exp_list
            e_loc expected_k h is_total handlers expected_pat_ty expected_ty in
        mh.is_total <- is_total;
        expected_ty, Kind.sup actual_pat_k actual_k_h
    | Epresent { handlers; default_opt } ->
        let expected_ty = new_var () in
        let actual_k =
          present_handler_exp_list
            e_loc expected_k h handlers default_opt expected_ty in
        expected_ty, actual_k
    | Ereset(e_body, e_res) ->
       let ty, actual_k_body = expression expected_k h e_body in
       let actual_k = expect expected_k h e_res Initial.typ_bool in
       ty, Kind.sup actual_k_body actual_k
    | Eassert(e_body) ->
       let actual_k = expect expected_k h e Initial.typ_bool in
       Initial.typ_unit, actual_k
    | Elocal(b, e_body) ->
       let _, new_h, _, actual_k = block_eq expected_k h b in
       let ty, actual_k_e = expression expected_k h e_body in
       ty, Kind.sup actual_k actual_k_e
    | Esizeapp _ ->
       Misc.not_yet_implemented "typing for size functions"
    | Eforloop _ ->
       Misc.not_yet_implemented "typing for for-loops" in
  e.e_info <- Typinfo.set_type e.e_info ty;
  ty, actual_k

and type_label_arg expected_k expected_ty h loc ({ label; arg } as r) =
  let qualid, { label_arg = ty_arg; label_res = ty_res } =
    get_label loc label in
  unify_expr arg expected_ty ty_arg;
  let actual_k = expect expected_k h arg ty_res in
  r.label <- Lident.Modname(qualid);
  actual_k

(** The type of primitives and imported functions **)
and operator expected_k h loc op e_list =
  let actual_k, ty_args, ty_res =
    match op with
    | Eifthenelse ->
        let ty = new_var () in
        Tfun(Tconst), [Initial.typ_bool; ty; ty], ty
    | Eunarypre ->
        let ty = new_var () in
        Tnode(Tdiscrete), [ty], ty
    | (Eminusgreater | Efby) ->
        let ty = new_var () in
        Tnode(Tdiscrete), [ty; ty], ty
    | Erun _ ->
       let ty_arg = new_var () in
       let ty_res = new_var () in
       let ty_f = Types.arrowtype expected_k None ty_arg ty_res in
       expected_k, [ty_f; ty_arg], ty_res
    | Eseq ->
       let ty = new_var () in
       Tfun(Tconst), [Initial.typ_unit; ty], ty
    | Eatomic ->
       let ty = new_var () in
       Tfun(Tconst), [ty], ty
    | Etest ->
       let ty = new_var () in
       Tfun(Tconst), [Initial.typ_signal ty], Initial.typ_bool
    | Eup ->
       Tnode(Tcont), [Initial.typ_float], Initial.typ_zero
    | Eperiod ->
       Tfun(Tconst), [Initial.typ_float; Initial.typ_float], Initial.typ_zero
    | Ehorizon ->
       Tnode(Tcont), [Initial.typ_float], Initial.typ_zero
    | Edisc ->
       Tnode(Tcont), [Initial.typ_float], Initial.typ_zero
    | Earray(op) ->
       let actual_k, ty_args, ty_res =
         match op with
         | Earray_list ->
            let ty = new_var () in
            Tfun(Tconst), List.map (fun _ -> ty) e_list, Initial.typ_array ty
         | Econcat ->
            let ty = Initial.typ_array (new_var ()) in
            Tfun(Tconst), [ty; ty], ty
         | Eget ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty; Initial.typ_int], ty
         | Eget_with_default ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty; Initial.typ_int; ty], ty
         | Eslice ->
            let ty = Initial.typ_array (new_var ()) in
            Tfun(Tconst), [ty; ty], ty
         | Eupdate ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty; Initial.typ_int; ty],
            Initial.typ_array ty
         | Etranspose ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array (Initial.typ_array ty)],
            Initial.typ_array (Initial.typ_array ty)
         | Ereverse ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array ty], Initial.typ_array ty
         | Eflatten ->
            let ty = new_var () in
            Tfun(Tconst), [Initial.typ_array (Initial.typ_array ty)],
            Initial.typ_array ty in
       actual_k, ty_args, ty_res in
  less_than loc actual_k expected_k;
  let actual_k_list =
    List.map2 (expect expected_k h) e_list ty_args in
  ty_res, Kind.sup actual_k (Kind.sup_list actual_k_list)

and funexp expected_k h ({ f_vkind; f_kind; f_args; f_body; f_loc } as body) =
  (* typing the argument of a function *)
  let arg_list expected_k h f_args =
    (* typing an argument. An argument is a list of vardec declarations *)
    let arg (h, acc_h) v_list =
      let h_arg, actual_k = vardec_list expected_k h v_list in
      let ty = type_of_vardec_list v_list in
      let n_opt =
        (* a dependence is allowed only when the input is a name *)
        match v_list with | [ { var_name } ] -> Some(var_name) | _ -> None in
      (n_opt, ty), (Env.append h_arg h, Env.append h_arg acc_h) in
    Util.mapfold arg (h, Env.empty) f_args in
  
  let expected_body_k = Interface.kindtype f_kind in
  let expected_args_v = Interface.vkindtype f_vkind in
  let actual_k, expected_body_k =
   kind_of_funexp f_loc expected_k expected_args_v expected_body_k in
  let h = Env.on h expected_k in
  let name_ty_arg_list, (h, h_args) = arg_list expected_body_k h f_args in
  body.f_env <- h_args;
  (* type the body *)
  let ty_res, _ = result expected_body_k h f_body in
  (* returns a type *)
  arrowtype f_loc expected_body_k name_ty_arg_list ty_res,
  actual_k

(* typing the result of a function *)
and result expected_k h ({ r_desc } as r) =
  let ty, actual_k =
    match r_desc with
    | Exp(e) ->
       let ty, actual_k = expression expected_k h e in
       ty, actual_k
    | Returns ({ b_vars } as b) ->
       let _, new_h, _, actual_k = block_eq expected_k h b in
       type_of_vardec_list b_vars, actual_k in
  (* type annotation *)
  r.r_info <- Typinfo.set_type r.r_info ty;
  ty, actual_k

(* Typing an expression with expected type [expected_type] **)
and expect expected_k h e expected_ty =
  let actual_ty, actual_k = expression expected_k h e in
  unify_expr e expected_ty actual_ty;
  actual_k


(** Typing an application **)
and apply loc expected_k h f arg_list =
  (* first type the function body *)
  let ty_fct, actual_k_fct = expression expected_k h f in
  (* typing the list of arguments *)
  let rec args actual_k_fct ty_fct = function
    | [] -> ty_fct, actual_k_fct
    | arg :: arg_list ->
       let arg_k, n_opt, ty1, ty2 =
         try Types.filter_arrow (Tfun(Tany)) ty_fct
         with Unify -> error loc (Eapplication_of_non_function) in
       let expected_arg_k =
         match arg_k with
         | Tfun(Tconst) | Tfun(Tstatic) -> arg_k
         | _ -> expected_k in
       let actual_k_arg = expect expected_arg_k h arg ty1 in
       let actual_k_fct =
         match actual_k_fct, arg_k with
         (* |-const f : t -A-> t' and |-k e: t then |-k f e: t' *)
         | Tfun(Tconst), Tfun _ -> actual_k_arg
         (* |-static f : t -A-> t' and |-k e: t then |-static\/k f e: t' *)
         | Tfun(Tstatic), Tfun _ -> Kind.sup actual_k_fct actual_k_arg
         | _ -> Kind.sup actual_k_fct (Kind.sup arg_k actual_k_arg) in
       (* check that the actual kind is less than the expected one *)
       less_than loc actual_k_fct expected_k;
       let ty2 =
         match n_opt with
         | None -> ty2
         | Some(n) -> subst_in_type (Env.singleton n (size_of_exp arg)) ty2 in
       args actual_k_fct ty2 arg_list in
  args actual_k_fct ty_fct arg_list

(** Typing an equation. Returns the set of defined names **)
and equation expected_k h { eq_desc; eq_loc } =
  match eq_desc with
  | EQeq(p, e) ->
     let ty_e, actual_k = expression expected_k h e in
     pattern h p ty_e;
     (* check that the pattern is total *)
     check_total_pattern p;
     let dv = Write.fv_pat S.empty p in
     { Defnames.empty with dv = dv }, actual_k
  | EQder { id; e; e_opt; handlers } ->
     (* a derivative is only possible in a stateful context *)
     less_than eq_loc (Tnode(Tcont)) expected_k;
     let actual_ty = derivative eq_loc h id in
     let _ = expect expected_k h e actual_ty in
     unify eq_loc Initial. typ_float actual_ty;
     let di =
       match e_opt with
       | None -> S.empty
       | Some(e) ->
          let _ = expect expected_k h e Initial.typ_float in
          let _ = init eq_loc h id in S.singleton id in
     ignore (present_handler_exp_list
               eq_loc expected_k h handlers NoDefault Initial.typ_float);
     { Defnames.empty with di = di; der = S.singleton id }, Tnode(Tcont)
  | EQinit(n, e0) ->
     (* an initialization is valid only in a stateful context *)
     stateful eq_loc expected_k;
     let actual_ty = init eq_loc h n in
     let _ = expect expected_k h e0 actual_ty in
     { Defnames.empty with di = S.singleton n }, expected_k
  | EQemit(n, e_opt) ->
     let ty_e = new_var () in
     let actual_ty = Types.instance (typ_of_var eq_loc h n) in
     let actual_k =
       match e_opt with
       | None ->
          unify eq_loc (Initial.typ_signal Initial.typ_unit) actual_ty;
          Tfun(Tconst)
       | Some(e) ->
          unify eq_loc (Initial.typ_signal ty_e) actual_ty;
          expect expected_k h e ty_e in
     { Defnames.empty with dv = S.singleton n }, actual_k
  | EQautomaton({ is_weak; handlers; state_opt }) ->
     (* automata are only valid in a statefull context *)
     stateful eq_loc expected_k;
     automaton_handlers_eq is_weak eq_loc expected_k h handlers state_opt
  | EQmatch({ is_total; e; handlers } as mh) ->
     let expected_pat_ty, actual_k_e = expression expected_k h e in
     let is_total, defnames, actual_k_h =
       match_handler_eq_list
         eq_loc expected_k h is_total handlers expected_pat_ty in
     mh.is_total <- is_total;
     defnames, Kind.sup actual_k_e actual_k_h
  | EQif { e; eq_true; eq_false } ->
     let actual_k_e = expect expected_k h e Initial.typ_bool in
     let defnames1, actual_k_eq_true = equation expected_k h eq_true in
     let defnames2, actual_k_eq_false = equation expected_k h eq_false in
     Total.merge eq_loc h [defnames1; defnames2],
     Kind.sup actual_k_e (Kind.sup actual_k_eq_true actual_k_eq_false)
  | EQpresent({ handlers; default_opt }) ->
     present_handler_eq_list eq_loc expected_k h handlers default_opt
  | EQreset(eq, e) ->
     let actual_k_e = expect expected_k h e Initial.typ_bool in
     let defnames, actual_k_eq =
       equation expected_k h eq in
     defnames, Kind.sup actual_k_e actual_k_eq
  | EQand { eq_list } -> equation_list expected_k h eq_list
  | EQempty -> Defnames.empty, Tfun(Tconst)
  | EQlocal(b_eq) ->
     let _, _, defnames, actual_k = block_eq expected_k h b_eq in
     defnames, actual_k
  | EQlet(l_eq, eq) ->
     let h, actual_k = leq expected_k h l_eq in
     let defnames, actual_k_eq = equation expected_k h eq in
     defnames, Kind.sup actual_k actual_k_eq
  | EQassert(e) ->
     let actual_k = expect expected_k h e Initial.typ_bool in
     Defnames.empty, actual_k
  | EQforloop _ ->
     Misc.not_yet_implemented "typing for for-loops"
  | EQsizefun _ ->
     Misc.not_yet_implemented "typing for size functions"

and equation_list expected_k h eq_list =
  List.fold_left
    (fun (defined_names, actual_k) eq ->
      let defined_names_eq, actual_k_eq = equation expected_k h eq in
      Total.join eq.eq_loc defined_names_eq defined_names,
    Kind.sup actual_k_eq actual_k)
    (Defnames.empty, Tfun(Tconst)) eq_list

(** Type a present handler when the body is an expression or equation **)
and present_handler_exp_list loc expected_k h p_h_list default_opt expected_ty =
  let _, actual_k =
    present_handlers scondpat
      (fun expected_k h e expected_ty ->
        let actual_k = expect expected_k h e expected_ty in
        Defnames.empty, actual_k)
      loc expected_k h p_h_list default_opt expected_ty in
  actual_k

and present_handler_eq_list loc expected_k h eq_h_list eq_opt =
  present_handlers scondpat
    (fun expected_k h eq _ -> equation expected_k h eq)
    loc expected_k h eq_h_list eq_opt Initial.typ_unit

(** Type a match handler when the body is an expression or equation **)
and match_handler_eq_list loc expected_k h is_total eq_h_list pat_ty =
  match_handlers
    (fun expected_k h eq _ -> equation expected_k h eq)
    loc expected_k h is_total eq_h_list pat_ty Initial.typ_unit

and match_handler_exp_list loc expected_k h total m_h_list pat_ty ty =
  let is_total, _, actual_k =
    match_handlers
      (fun expected_k h e expected_ty ->
        let actual_k = expect expected_k h e expected_ty in
        Defnames.empty, actual_k)
      loc expected_k h total m_h_list pat_ty ty in
  is_total, actual_k

(** Type an automaton handler when the body is an equation **)
and automaton_handlers_eq is_weak loc expected_k h handlers se_opt =
  let block_eq expected_k h ({ b_vars; b_body } as b) =
    let _, h, defined_names, actual_k = block_eq expected_k h b in
    h, defined_names, actual_k in
  let defined_names, _ =
    automaton_handlers scondpat leqs block_eq block_eq state_expression
      is_weak loc expected_k h handlers se_opt in
  (* the actual kind is necessarily stateful *)
  defined_names, expected_k

and block_eq expected_k h ({ b_vars; b_body = { eq_write } as b_body } as b) =
  let h0, actual_k_h0 = vardec_list expected_k h b_vars in
  (* if [init x = ...] appears in [b_body], update [h0] *)
  let h0 = add_init_eq_of_env h0 eq_write in
  let h = Env.append h0 h in
  let defined_names, actual_k_body = equation expected_k h b_body in
  (* check that every name in [n_list] has a definition *)
  let defined_names =
    check_definitions_for_every_name defined_names b_vars in
  b.b_env <- h0;
  b.b_write <- defined_names;
  h0, h, defined_names, Kind.sup actual_k_h0 actual_k_body

and leq expected_k h ({ l_kind; l_eq; l_loc } as l) =
  (* in a static or constant context all introduced names inherits it *)
  let expected_k = Kind.inherits expected_k (Interface.vkindtype l_kind) in
  Misc.push_binding_level ();
  let h0 = env_of_equation expected_k l_eq in
  (* because names are unique, typing of [l_eq] is done with [h+h0] *)
  let new_h = Env.append h0 h in
  let _, actual_k = equation expected_k new_h l_eq in
  Misc.pop_binding_level ();
  let is_gen = not (expansive l_eq) in
  let h0 = Types.gen_decl is_gen h0 in
  (* check that the type for every entry has the right kind *)
  check_type_is_in_kind l_loc h0 (Kind.vkind l_kind);
  l.l_env <- h0;
  new_h, actual_k

and leqs expected_k h l =
  List.fold_left
    (fun (h, acc_k) l_eq ->
      let h, actual_k = leq expected_k h l_eq in
      h, Kind.sup acc_k actual_k) (h, Tfun(Tconst)) l
  
(** Typing a signal condition **)
and scondpat expected_k type_of_condition h scpat =
  let rec typrec expected_k scpat =
    match scpat.desc with
    | Econdand(sc1, sc2) ->
       let actual_k1 = typrec expected_k sc1 in
       let actual_k2 = typrec expected_k sc2 in
       Kind.sup actual_k1 actual_k2
    | Econdor(sc1, sc2) ->
       let actual_k1 = typrec expected_k sc1 in
       let actual_k2 = typrec expected_k sc2 in
       Kind.sup actual_k1 actual_k2
    | Econdexp(e) ->
       expect expected_k h e type_of_condition
    | Econdpat(e_cond, pat) ->
       (* check that e is a signal *)
       let ty = new_var () in
       let actual_k = expect expected_k h e_cond (Initial.typ_signal ty) in
       pattern h pat ty;
       actual_k
    | Econdon(sc1, e) ->
       let actual_k1 = typrec expected_k sc1 in
       (* we impose that [e] is a combinatorial expression *)
       (* not to have state variable that evolve only when [sc1] is true *)
       let actual_k = expect (Tfun(Tany)) h e Initial.typ_bool in
       Kind.sup actual_k1 actual_k in
  typrec expected_k scpat


(* typing state expressions. [state] must be a stateless expression *)
(* [actual_reset = true] if [state] is entered by reset *)
and state_expression h def_states actual_reset { desc; loc } = 
  match desc with
  | Estate0(s) ->
     begin try
         let ({ s_reset = expected_reset; s_parameters = args } as r) =
           Env.find s def_states in
         if args <> []
         then error loc (Estate_arity_clash(s, 0, List.length args));
         r.s_reset <-
           check_target_state loc expected_reset actual_reset;
         Tfun(Tconst)
       with
       | Not_found -> error loc (Estate_unbound s)
     end
  | Estate1(s, l) ->
     let ({ s_reset = expected_reset; s_parameters = args } as r) =
       try
         Env.find s def_states
       with
       | Not_found -> error loc (Estate_unbound s) in
     begin try
         (* we impose that [e] is combinatorial *)
         let actual_k_list =
           List.map2
             (fun e expected_ty -> expect (Tfun(Tany)) h e expected_ty)
             l args in
         r.s_reset <-
           check_target_state loc expected_reset actual_reset;
         Kind.sup_list actual_k_list
       with
       | Invalid_argument _ ->
          error loc
            (Estate_arity_clash(s, List.length l, List.length args))
     end
  | Estateif(e, se1, se2) ->
     (* we impose that [e] is combinatorial *)
     let actual_k = expect (Tfun(Tany)) h e Initial.typ_bool in
     let actual_k1 = state_expression h def_states actual_reset se1 in
     let actual_k2 = state_expression h def_states actual_reset se2 in
     Kind.sup actual_k (Kind.sup actual_k1 actual_k2)

     
let implementation ff is_first { desc; loc } =
  try
    match desc with
    | Eopen(modname) ->
       if is_first then Modules.open_module modname
    | Eletdecl { d_leq } ->
       let new_h, actual_k = leq (Tfun(Tconst)) Env.empty d_leq in
       (* check that there is no unbounded size variables *)
       check_no_unbounded_size_name loc new_h;
       (* update the global environment *)
       if is_first then
         Env.iter
           (fun name { t_tys; t_path } ->
             Interface.add_type_of_value ff loc
               (Ident.source name) (Kind.is_const t_path) t_tys) new_h
       else
         Env.iter
           (fun name { t_tys; t_path } ->
             Interface.update_type_of_value ff loc
               (Ident.source name) (Kind.is_const t_path) t_tys) new_h
    | Etypedecl { name; ty_params; ty_decl } ->
       if is_first then
         Interface.typedecl ff loc name ty_params ty_decl
  with
  | Typerrors.Error(loc, err) ->
     if is_first then Typerrors.message loc err
     else
       begin
         Format.eprintf
           "@[Internal error: type error during the second step \n\
            after static reduction and inlining\n\
            Be carreful, the localisation of errors is misleading@.@.@]";
         Typerrors.message loc err
       end

(* the main entry function *)
let program ff is_first ({ p_impl_list } as p) =
  (* turn off warning when not the first typing step *)
  Misc.no_warning := not is_first;
  List.iter (implementation ff is_first) p_impl_list;
  Misc.no_warning := not is_first;
  p

