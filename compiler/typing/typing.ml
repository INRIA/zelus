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
open Deftypes
open Types
open Typerrors

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
  
let type_is_in_kind loc actual_k ty =
  if not (Kind.in_kind actual_k ty)
  then error loc (Etype_kind_clash(actual_k, ty))

let sort_less_than loc sort expected_k =
  match sort, expected_k with
  | Sstatic, _ -> ()
  | _, Tstatic -> error loc (Ekind_clash(Deftypes.Tfun, expected_k))
  | _ -> ()

(* An expression is expansive if it is an application *)
let rec expansive { e_desc = desc } =
  match desc with
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Efun _ -> false
  | Etuple(e_list) -> List.exists expansive e_list
  | Erecord(l_e_list) -> List.exists (fun { arg } -> expansive arg) l_e_list
  | Erecord_access { arg } | Etypeconstraint(arg, _) -> expansive arg
  | Erecord_with(e, l_e_list) ->
     expansive e || List.exists (fun { arg } -> expansive arg) l_e_list
  | _ -> true
       
(** The type of states in automata **)
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

(** Types for local identifiers *)
let var loc h n =
  try Env.find n h with | Not_found -> error loc (Evar_undefined(n))

let typ_of_var loc h n = let { t_typ } = var loc h n in t_typ

(* Typing [last n] *)
let last loc h n =
  let { t_sort; t_typ } as entry = var loc h n in
  entry.t_sort <- Deftypes.last t_sort;
  t_typ

let init loc h n =
  let { t_sort; t_typ } as entry = var loc h n in
  entry.t_sort <- Deftypes.init t_sort;
  t_typ

let der loc h n =
  let { t_sort; t_typ } as entry = var loc h n in
  entry.t_sort <- Deftypes.cont t_sort;
  t_typ

(* Typing [n = ...] *)
let def loc h n =
  let { t_typ } as entry = var loc h n in
  t_typ

(** Types for global identifiers *)
let global loc lname =
  let { qualid; info = { value_typ = tys } } = find_value loc lname in
  qualid, Types.instance_of_type tys

let global_with_instance loc lname =
  let { qualid; info = { value_typ = tys } } = find_value loc lname in
  let typ_instance, typ_body = Types.instance_and_vars_of_type tys in
  qualid, typ_instance, typ_body

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

(* Computes the type list from a vardec list *)
let type_of_vardec_list h n_list =
  let type_of_vardec { var_typ } = var_typ in
  let ty_list = List.map type_of_vardec n_list in
  match ty_list with
  | [] -> Initial.typ_unit
  | _ -> Types.product ty_list

let tentry sort =
  { t_typ = Types.new_var (); t_default = None; t_init = None; t_sort = sort }
 
let env_of_pattern acc pat =
  let entry x acc = Env.add x (tentry Sval) acc in
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

let env_of_scondpat scpat =
  let rec env_of acc { desc } =
    match desc with
    | Econdand(sc1, sc2) -> env_of (env_of acc sc1) sc2
    | Econdor(sc, _) | Econdon(sc, _) -> env_of acc sc
    | Econdexp _ -> acc
    | Econdpat(_, pat) -> env_of_pattern acc pat in
  env_of Env.empty scpat
 
and env_of_statepat spat =
  let env_of acc { desc } =
    match desc with
    | Estate0pat _ -> acc
    | Estate1pat(_, l) -> List.fold_left (fun acc n -> S.add n acc) acc l in
  let acc = env_of S.empty spat in
  S.fold (fun n acc -> Env.add n (tentry Sval) acc) acc Env.empty

let env_of_pattern pat = env_of_pattern Env.empty pat  

let env_of_equation { eq_write } =
  S.fold
    (fun n acc -> Env.add n (tentry Sval) acc)
    (Deftypes.names S.empty eq_write) Env.empty

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
       
(** Typing patterns **)
(* the kind of variables in [p] must be equal to [expected_k] *)
let rec pattern h ({ pat_desc; pat_loc } as pat) ty =
  match pat_desc with
  | Ewildpat ->
     (* type annotation *)
     pat.pat_typ <- ty
  | Econstpat(im) ->
     unify_pat pat ty (immediate im);
     (* type annotation *)
     pat.pat_typ <- ty
  | Econstr0pat(c0) ->
     let qualid, { constr_res = ty_res; constr_arity = n } =
       get_constr pat_loc c0 in
     (* check the arity *)
     if n <> 0 then error pat_loc (Econstr_arity(c0, n, 0));
     unify_pat pat ty ty_res;
     pat.pat_desc <- Econstr0pat(Lident.Modname(qualid));
     (* type annotation *)
     pat.pat_typ <- ty
  | Econstr1pat(c1, pat_list) ->
     let qualid,
         { constr_arg = ty_list; constr_res = ty_res; constr_arity = n } =
       get_constr pat_loc c1 in
     (* check the arity *)
     let actual_n = List.length pat_list in
     if n <> actual_n then error pat_loc (Econstr_arity(c1, n, actual_n));
     unify_pat pat ty ty_res;
     pat.pat_desc <- Econstr1pat(Lident.Modname(qualid), pat_list);
     (* type annotation *)
     pat.pat_typ <- ty;
     List.iter2 (pattern h) pat_list ty_list
  | Evarpat(x) ->
     unify_pat pat ty (typ_of_var pat_loc h x);
     (* type annotation *)
     pat.pat_typ <- ty
  | Etuplepat(pat_list) ->
     let ty_list = List.map (fun _ -> new_var ()) pat_list in
     unify_pat pat ty (product ty_list);
     (* type annotation *)
     pat.pat_typ <- ty;
     List.iter2 (pattern h) pat_list ty_list
  | Etypeconstraintpat(p, typ_expr) ->
     let expected_typ =
       Types.instance_of_type(Interface.scheme_of_type typ_expr) in
     unify_pat pat expected_typ ty;
     (* type annotation *)
     pat.pat_typ <- ty;
     pattern h p ty
  | Erecordpat(label_pat_list) ->
     (* type annotation *)
     pat.pat_typ <- ty;
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
     unify_pat pat ty (typ_of_var pat_loc h x);
     (* type annotation *)
     pat.pat_typ <- ty;
     pattern h p ty
  | Eorpat(p1, p2) ->
     (* type annotation *)
     pat.pat_typ <- ty;
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
let match_handlers body loc expected_k h is_total m_handlers pat_ty ty =
  let handler ({ m_pat = pat; m_body = b } as mh) =
    let h0 = env_of_pattern pat in
    pattern h0 pat pat_ty;
    mh.m_env <- h0;
    let h = Env.append h0 h in
    let defined_names, actual_k = body expected_k h b ty in
    defined_names, actual_k in
  let defined_names_k_list = List.map handler m_handlers in
  let defined_names_list, k_list = List.split defined_names_k_list in

  (* check partiality/redundancy of the pattern matching *)

  let is_total =
    is_total || (Patternsig.check_match_handlers loc m_handlers) in

  let defined_names_list =
    if is_total then defined_names_list
    else Deftypes.empty :: defined_names_list in
  (* identify variables which are defined partially *)
  is_total,
  Total.merge loc h defined_names_list,
  (* the kind is the sup of all kinds *)
  Kind.sup_list k_list

(** Typing a present handler. *)
(*- Returns defined names and the kind is the supremum *)
let present_handlers scondpat body loc expected_k h h_list opt expected_ty =
  let handler ({ p_cond; p_body } as ph) =
    (* local variables from [scpat] cannot be accessed through a last *)
    let h0 = env_of_scondpat p_cond in
    let h = Env.append h0 h in
    let actual_k_spat = scondpat expected_k Initial.typ_bool h p_cond in
    ph.p_env <- h0;
    let defined_names, actual_k = body expected_k h p_body expected_ty in
    defined_names, Kind.sup actual_k_spat actual_k in

  let defined_names_k_list = List.map handler h_list in
  let defined_names_list, k_list = List.split defined_names_k_list in

  (* treat the optional default case *)
  let defined_names_list, actual_k =
    match opt with
    | NoDefault -> Deftypes.empty :: defined_names_list, Tstatic
    | Init(b) ->
       let defined_names, _ = body expected_k h b expected_ty in
       less_than loc Tnode expected_k;
       defined_names :: defined_names_list, Tnode
    | Else(b) ->
       let defined_names, actual_k = body expected_k h b expected_ty in
       defined_names :: defined_names_list, actual_k in
                          
  (* identify variables which are defined partially *)
  Total.merge loc h defined_names_list,
  Kind.sup actual_k (Kind.sup_list k_list)

(** Typing an automaton. Returns defined names **)
let rec automaton_handlers
          scondpat leqs body body_escape state_expression
          is_weak loc (expected_k: Deftypes.kind) h handlers se_opt =
  (* check that all declared states are accessible *)
  Total.Automaton.check_all_states_are_accessible loc handlers;

  (* global table which associate the set of defined_names for every state *)
  let t = Total.Automaton.table handlers in

  (* build the environment of states. *)
  let addname acc { s_state = statepat } =
    match statepat.desc with
      | Estate0pat(s) -> Env.add s { s_reset = None; s_parameters = [] } acc
      | Estate1pat(s, l) ->
          Env.add s { s_reset = None;
                      s_parameters = (List.map (fun _ -> new_var ()) l)} acc in
  let def_states = List.fold_left addname Env.empty handlers in

  (* in case [se_opt = None], checks that the initial state is a non *)
  (* parameterised state. *)
  let { s_state = statepat } = List.hd handlers in
  let actual_k_init =
    match se_opt with
    | None ->
       begin match statepat.desc with
       | Estate1pat _ -> error statepat.loc Estate_initial
       | Estate0pat _ -> Tstatic
       end
    | Some(se) -> state_expression h def_states true se in
  
  (* the type for conditions on transitions *)
  let type_of_condition = Initial.typ_bool in

  (* typing the body of the automaton *)
  let typing_handler h ({ s_state; s_let; s_body; s_trans } as s) =
    let escape source_state h expected_k
        ({ e_cond; e_reset; e_let; e_body; e_next_state } as esc) =
      (* type one escape condition *)
      let h0 = env_of_scondpat e_cond in
      let h = Env.append h0 h in
      let actual_k_e_cond = scondpat expected_k type_of_condition h e_cond in
      esc.e_env <- h0;
      (* type check the sequence of local equations *)
      let h, actual_k_let = leqs expected_k h e_let in
      (* type check the body *)
      let h, defined_names, actual_k_body =
        body_escape expected_k h e_body in
      (* checks that [state] belond to the current set of [states] *)
      let actual_k_state = state_expression h def_states e_reset e_next_state in
      (* checks that names are not defined twice in a state *)
      let state_names =
        if is_weak then S.singleton source_state
        else Total.Automaton.statenames e_next_state in
      Total.Automaton.add_transitions is_weak h state_names defined_names t;
      Kind.sup actual_k_e_cond
        (Kind.sup actual_k_let (Kind.sup actual_k_body actual_k_state)) in

    (* typing the state pattern *)
    let h0 = env_of_statepat s_state in
    s.s_env <- h0;
    begin match s_state.desc with
    | Estate0pat _ -> ()
    | Estate1pat(s, n_list) ->
       let { s_parameters = ty_list } = Env.find s def_states in
       List.iter2
         (fun n ty ->
           unify s_state.loc
             (typ_of_var s_state.loc h0 n) ty) n_list ty_list;
    end;
    let h = Env.append h0 h in
    (* type check the sequence of local equations *)
    let h, actual_k_let = leqs expected_k h s_let in
    (* typing the body *)
    let new_h, defined_names, actual_k_body =
      body expected_k h s_body in
    (* add the list of defined_names to the current state *)
    let source_state = Total.Automaton.statepatname statepat in
    Total.Automaton.add_state source_state defined_names t;
    let actual_k_list =
      List.map (escape source_state new_h expected_k) s_trans in
    let actual_k =
      Kind.sup (Kind.sup_list actual_k_list)
        (Kind.sup actual_k_let actual_k_init) in
    defined_names, actual_k in

  let defined_names_k_list = List.map (typing_handler h) handlers in
  let defined_names_list, k_list = List.split defined_names_k_list in

  (* identify variables which are partially defined in some states *)
  (* and/or transitions *)
  let defined_names = Total.Automaton.check loc h t in
  (* write defined_names in every handler *)
  List.iter2
    (fun { s_body = { b_write = _ } as b } defined_names ->
      b.b_write <- defined_names)
    handlers (defined_names :: defined_names_list);

  (* finally, indicate for every state handler if it is entered *)
  (* by reset or not *)
  mark_reset_state def_states handlers;
  let actual_k = Kind.sup_list k_list in
  defined_names, Kind.sup actual_k_init actual_k

(* Once the body of an automaton has been typed, indicate for every *)
(* handler if it is always entered by reset or not *)
and mark_reset_state def_states handlers =
  let mark ({ s_state } as handler) =
    let { s_reset = r } =
      Env.find (Total.Automaton.statepatname s_state) def_states in
    let v = match r with | None | Some(false) -> false | Some(true) -> true in
    handler.Zelus.s_reset <- v in
  List.iter mark handlers


(* Typing the declaration of variables. The result is a typing environment *)
let rec vardec_list expected_k h n_list =
  (* typing every declaration *)
  let vardec (acc_h, acc_k)
        ({ var_name; var_default; var_init; var_clock;
          var_typeconstraint; var_loc } as v) =
    let expected_ty = Types.new_var () in
    let actual_k =
      Util.optional_with_default
        (fun e -> expect expected_k h e expected_ty) Tstatic var_default in
    (* the initialization must appear in a statefull function *)
    let actual_k_init =
      Util.optional_with_default
        (fun e -> less_than e.e_loc Tnode expected_k;
                  let _ = expect expected_k h e expected_ty in
                  Tnode) Tstatic var_init in
    let actual_k = Kind.sup actual_k actual_k_init in
    let entry =
      { t_sort = Sval; t_default = var_default;
        t_init = var_init; t_typ = expected_ty } in
    (* type annotation *)
    v.var_typ <- expected_ty;
    Env.add var_name entry acc_h,
    Kind.sup actual_k (Kind.sup actual_k_init acc_k) in
  List.fold_left vardec (Env.empty, Tstatic) n_list

(* [expression expected_k h e] returns the type for [e] and [actual kind] *)
and expression expected_k h ({ e_desc; e_loc } as e) =
  let ty, actual_k = match e_desc with
    | Econst(i) -> immediate i, Tstatic
    | Elocal(x) ->
       let { t_typ = typ; t_sort = sort } = var e_loc h x in
       sort_less_than e_loc sort expected_k;
       typ, Kind.kind_of sort
    | Eglobal ({ lname = lname } as g) ->
       let qualid, typ_instance, ty =
         global_with_instance e_loc lname in
       g.lname <- Lident.Modname(qualid);
       g.typ_instance <- typ_instance;
       ty, Tstatic
    | Elast(x) -> last e_loc h x, Tfun
    | Etuple(e_list) ->
       let ty_k_list = List.map (expression expected_k h) e_list in
       let ty_list, k_list = List.split ty_k_list in
       product ty_list, Kind.sup_list k_list
    | Eop(op, e_list) ->
       operator expected_k h e_loc op e_list
    | Eapp(f, arg_list) ->
       apply e_loc expected_k h f arg_list
    | Econstr0({ lname } as c) ->
       let qualid, { constr_res = ty_res; constr_arity = n } =
         get_constr e_loc lname in
       if n <> 0 then error e_loc (Econstr_arity(lname, n, 0));
       c.lname <- Lident.Modname(qualid);
       ty_res, Tstatic
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
         Types.instance_of_type (Interface.scheme_of_type typ_expr) in
       let actual_k = expect expected_k h exp expected_typ in
       expected_typ, actual_k
    | Elet(l, e) ->
       let h, actual_k = leq expected_k h l in
       let ty, actual_k_e = expression expected_k h e in
       ty, Kind.sup actual_k actual_k_e
    | Efun(fe) ->
       (* functions are only allowed in a static context *)
       less_than e_loc expected_k Tstatic;
       let ty = funexp h fe in
       ty, Tstatic
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
       Initial.typ_unit, actual_k in
  (* type annotation *)
  e.e_typ <- ty;
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
        Tfun, [Initial.typ_bool; ty; ty], ty
    | Eunarypre ->
        let ty = new_var () in
        Tnode, [ty], ty
    | (Eminusgreater | Efby) ->
        let ty = new_var () in
        Tnode, [ty; ty], ty
    | Erun _ ->
       let ty1 = new_var () in
       let ty2 = new_var () in
       Tnode, [ty1], ty2
    | Eseq ->
       let ty = new_var () in
       Tfun, [Initial.typ_unit; ty], ty
    | Eatomic ->
       let ty = new_var () in
       Tfun, [ty], ty
    | Etest ->
       let ty = new_var () in
       Tfun, [Initial.typ_signal ty], Initial.typ_bool
    | Eup ->
       Tnode, [Initial.typ_float], Initial.typ_zero
    | Eperiod ->
       Tstatic, [Initial.typ_float; Initial.typ_float], Initial.typ_zero
    | Ehorizon ->
       Tnode, [Initial.typ_float], Initial.typ_zero
    | Edisc ->
       Tnode, [Initial.typ_float], Initial.typ_zero
    | Earray(op) ->
       let actual_k, ty_args, ty_res =
         match op with
         | Earray_list ->
            let ty = new_var () in
            Tfun, List.map (fun _ -> ty) e_list, Initial.typ_array ty
         | Econcat ->
            let ty = Initial.typ_array (new_var ()) in
            Tfun, [ty; ty], ty
         | Eget ->
            let ty = new_var () in
            Tfun, [Initial.typ_array ty; Initial.typ_int], ty
         | Eget_with_default ->
            let ty = new_var () in
            Tfun, [Initial.typ_array ty; Initial.typ_int; ty], ty
         | Eslice ->
            let ty = Initial.typ_array (new_var ()) in
            Tfun, [ty; ty], ty
         | Eupdate ->
            let ty = new_var () in
            Tfun, [Initial.typ_array ty; Initial.typ_int; ty],
            Initial.typ_array ty
         | Etranspose ->
            let ty = new_var () in
            Tfun, [Initial.typ_array (Initial.typ_array ty)],
            Initial.typ_array (Initial.typ_array ty)
         | Ereverse ->
            let ty = new_var () in
            Tfun, [Initial.typ_array ty], Initial.typ_array ty
         | Eflatten ->
            let ty = new_var () in
            Tfun, [Initial.typ_array (Initial.typ_array ty)],
            Initial.typ_array ty in
       actual_k, ty_args, ty_res in
  less_than loc actual_k expected_k;
  let actual_k_list =
    List.map2 (expect expected_k h) e_list ty_args in
  ty_res, Kind.sup actual_k (Kind.sup_list actual_k_list)

and funexp h ({ f_kind; f_args; f_body } as body) =
  let expected_k = Interface.kindtype f_kind in
  let h_args, _, ty_arg_list = arg_list expected_k h f_args in
  body.f_env <- h_args;
  (* type the body *)
  let h = Env.append h_args h in
  let ty_res, _ = result expected_k h f_body in
  (* returns a type *)
  Types.arrowtype_list expected_k ty_arg_list ty_res

and arg_list expected_k h args =
  let h_args, actual_k_args =
    List.fold_left
      (fun (acc_h, acc_k) arg -> vardec_list expected_k h arg)
      (Env.empty, Tstatic) args in
  let ty_args =
    List.map (type_of_vardec_list h_args) args in
  h_args, actual_k_args, ty_args
  
(* Typing the result of a function *)
and result expected_k h ({ r_desc } as r) =
  let ty, actual_k =
    match r_desc with
    | Exp(e) ->
       let ty, actual_k = expression expected_k h e in
       ty, actual_k
    | Returns ({ b_vars } as b) ->
       let _, new_h, _, actual_k = block_eq expected_k h b in
       type_of_vardec_list new_h b_vars, actual_k in
  (* type annotation *)
  r.r_typ <- ty;
  ty, actual_k

(* Typing an expression with expected type [expected_type] **)
and expect expected_k h e expected_ty =
  let actual_ty, actual_k = expression expected_k h e in
  unify_expr e expected_ty actual_ty;
  actual_k

(** Typing an application **)
and apply loc expected_k h e arg_list =
  (* first type the function body *)
  let ty_fct, actual_k_fct = expression expected_k h e in
  (* typing the list of arguments *)
  let rec args actual_k_fct ty_fct = function
    | [] -> ty_fct, actual_k_fct
    | arg :: arg_list ->
       let arg_k, ty1, ty2 =
         try Types.filter_arrow Tfun ty_fct
         with Unify -> error loc (Eapplication_of_non_function) in
       let expected_k = match arg_k with | Tstatic -> Tstatic | _ -> expected_k in
       let actual_k_arg = expect expected_k h arg ty1 in
       let actual_k_fct =
         match actual_k_fct, arg_k, actual_k_arg with
         | Tstatic, Tfun, Tstatic -> Tstatic
         | _ -> Kind.sup actual_k_fct (Kind.sup arg_k actual_k_arg) in
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
     { Deftypes.empty with dv = dv }, actual_k
  | EQder(n, e, e0_opt, handlers) ->
     (* a derivative is only possible in a stateful context *)
     less_than eq_loc Tnode expected_k;
     let actual_ty = der eq_loc h n in
     let _ = expect expected_k h e actual_ty in
     unify eq_loc Initial. typ_float actual_ty;
     let di =
       match e0_opt with
       | None -> S.empty
       | Some(e) ->
          let _ = expect expected_k h e Initial.typ_float in
          let _ = init eq_loc h n in S.singleton n in
     ignore (present_handler_exp_list
               eq_loc expected_k h handlers NoDefault Initial.typ_float);
     { Deftypes.empty with di = di; der = S.singleton n }, Tnode
  | EQinit(n, e0) ->
     (* an initialization is valid only in a stateful context *)
     less_than eq_loc Tnode expected_k;
     let actual_ty = init eq_loc h n in
     let _ = expect expected_k h e0 actual_ty in
     { Deftypes.empty with di = S.singleton n }, Tnode
  | EQemit(n, e_opt) ->
     let ty_e = new_var () in
     let actual_ty = typ_of_var eq_loc h n in
     let actual_k =
       match e_opt with
       | None ->
          unify eq_loc (Initial.typ_signal Initial.typ_unit) actual_ty; Tstatic
       | Some(e) ->
          unify eq_loc (Initial.typ_signal ty_e) actual_ty;
          expect expected_k h e ty_e in
     { Deftypes.empty with dv = S.singleton n }, actual_k
  | EQautomaton({ is_weak; handlers; state_opt }) ->
     (* automata are only valid in a statefull context *)
     less_than eq_loc Tnode expected_k;
     automaton_handlers_eq is_weak eq_loc expected_k h handlers state_opt
  | EQmatch({ is_total; e; handlers } as mh) ->
     let expected_pat_ty, actual_k_e = expression expected_k h e in
     let is_total, defnames, actual_k_h =
       match_handler_eq_list
         eq_loc expected_k h is_total handlers expected_pat_ty in
     mh.is_total <- is_total;
     defnames, Kind.sup actual_k_e actual_k_h
  | EQif(e, eq1, eq2) ->
     let actual_k_e = expect expected_k h e Initial.typ_bool in
     let defnames1, actual_k_eq1 = equation expected_k h eq1 in
     let defnames2, actual_k_eq2 = equation expected_k h eq2 in
     Total.merge eq_loc h [defnames1; defnames2],
     Kind.sup actual_k_e (Kind.sup actual_k_eq1 actual_k_eq2)
  | EQpresent({ handlers; default_opt }) ->
     present_handler_eq_list eq_loc expected_k h handlers default_opt
  | EQreset(eq, e) ->
     let actual_k_e = expect expected_k h e Initial.typ_bool in
     let defnames, actual_k_eq =
       equation expected_k h eq in
     defnames, Kind.sup actual_k_e actual_k_eq
  | EQand(eq_list) -> equation_list expected_k h eq_list
  | EQempty -> Deftypes.empty, Tstatic
  | EQlocal(b_eq) ->
     let _, _, defnames, actual_k = block_eq expected_k h b_eq in
     defnames, actual_k
  | EQlet(l_eq, eq) ->
     let h, actual_k = leq expected_k h l_eq in
     let defnames, actual_k_eq = equation expected_k h eq in
     defnames, Kind.sup actual_k actual_k_eq
  | EQassert(e) ->
     let actual_k = expect expected_k h e Initial.typ_bool in
     Deftypes.empty, actual_k

and equation_list expected_k h eq_list =
  List.fold_left
    (fun (defined_names, actual_k) eq ->
      let defined_names_eq, actual_k_eq = equation expected_k h eq in
      Total.join eq.eq_loc defined_names_eq defined_names,
    Kind.sup actual_k_eq actual_k)
    (Deftypes.empty, Tstatic) eq_list

(** Type a present handler when the body is an expression or equation **)
and present_handler_exp_list loc expected_k h p_h_list default_opt expected_ty =
  let _, actual_k =
    present_handlers scondpat
      (fun expected_k h e expected_ty ->
        let actual_k = expect expected_k h e expected_ty in
        Deftypes.empty, actual_k)
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
        Deftypes.empty, actual_k)
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

and block_eq expected_k h ({ b_vars; b_body } as b) =
  let h0, actual_k_h0 = vardec_list expected_k h b_vars in
  let h = Env.append h0 h in
  let defined_names, actual_k_body = equation expected_k h b_body in
  (* check that every name in [n_list] has a definition *)
  let defined_names =
    check_definitions_for_every_name defined_names b_vars in
  b.b_env <- h0;
  b.b_write <- defined_names;
  h0, h, defined_names, Kind.sup actual_k_h0 actual_k_body

and leq expected_k h ({ l_rec; l_eq } as l) =
  let h0 = env_of_equation l_eq in
  l.l_env <- h0;
  let new_h = Env.append h0 h in
  let _, actual_k = equation expected_k new_h l_eq in
  new_h, actual_k

and leqs expected_k h l =
  List.fold_left
    (fun (h, acc_k) l_eq ->
      let h, actual_k = leq expected_k h l_eq in
      h, Kind.sup acc_k actual_k) (h, Tstatic) l
  
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
       let actual_k = expect Tfun h e Initial.typ_bool in
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
         Tstatic
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
         let actual_k_list =
           List.map2
             (fun e expected_ty -> expect Tfun h e expected_ty) l args in
         r.s_reset <-
           check_target_state loc expected_reset actual_reset;
         Kind.sup_list actual_k_list
       with
       | Invalid_argument _ ->
          error loc
            (Estate_arity_clash(s, List.length l, List.length args))
     end
  | Estateif(e, se1, se2) ->
     let actual_k = expect Tfun h e Initial.typ_bool in
     let actual_k1 = state_expression h def_states actual_reset se1 in
     let actual_k2 = state_expression h def_states actual_reset se2 in
     Kind.sup actual_k (Kind.sup actual_k1 actual_k2)

     
let implementation ff is_first { desc; loc } =
  try
    match desc with
    | Eopen(modname) ->
       if is_first then Modules.open_module modname
    | Eletdecl(f, e) ->
       Misc.push_binding_level ();
       (* a value a top level must be static. As it is the bottom kind *)
       (* no need to return it *)
       let ty, _ = expression Tstatic Env.empty e in
       (* check that the type is well formed *)
       type_is_in_kind loc Tstatic ty;
       Misc.pop_binding_level ();
       let tys = Types.gen (not (expansive e)) ty in
       if is_first then Interface.add_type_of_value ff loc f true tys
       else Interface.update_type_of_value ff loc f true tys
    | Etypedecl(f, params, ty) ->
       if is_first then Interface.typedecl ff loc f params ty
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
let program ff is_first impl_list =
  Misc.no_warning := not is_first;
  List.iter (implementation ff is_first) impl_list;
  Misc.no_warning := not is_first;
  impl_list

let implementation_list = program
