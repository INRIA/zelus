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

(* type checking *)

(* H  |-{k} e : t  and H, W |-{k} D *)
(* H : typing environment *)
(* D : set of variables written by D *)
(* k : either any, discrete, continuous *)
(* e : expression with type t       *)
(* input: H, e, k - output: t, W   *)

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


(** The main unification functions *)
let unify loc expected_ty actual_ty =
  try
    Types.unify expected_ty actual_ty
  with
    | Types.Unify -> error loc (Etype_clash(actual_ty, expected_ty))

let equal_sizes loc expected_size actual_size =
  try
    Types.equal_sizes expected_size actual_size
  with
    | Types.Unify -> error loc (Esize_clash(actual_size, expected_size))

let unify_expr expr expected_ty actual_ty =
  try
    Types.unify expected_ty actual_ty
  with
    | Types.Unify -> error expr.e_loc (Etype_clash(actual_ty, expected_ty))

let unify_pat pat expected_ty actual_ty =
  try
    Types.unify expected_ty actual_ty
  with
    | Types.Unify -> error pat.p_loc (Etype_clash(actual_ty, expected_ty))

let less_than loc actual_k expected_k =
  try
    Types.less_than actual_k expected_k
  with
    | Types.Unify -> error loc (Ekind_clash(actual_k, expected_k))

let type_is_in_kind loc expected_k ty =
  try
    Types.kind expected_k ty
  with
    | Types.Unify -> error loc (Etype_kind_clash(expected_k, ty))

let lift loc left_k right_k =
  try
    Types.lift left_k right_k
  with
  | Types.Unify -> error loc (Ekind_clash(right_k, left_k))

let sort_less_than loc sort expected_k =
  match expected_k, sort with
  | Tstatic _, Sstatic -> ()
  | Tstatic _, _ -> error loc (Ekind_clash(Deftypes.Tany, expected_k))
  | _ -> ()

let check_is_vec loc actual_ty =
  try
    let ty_arg, size = Types.filter_vec actual_ty in ty_arg, size
  with
    | Types.Unify -> error loc Esize_of_vec_is_undetermined

(* An expression is expansive if it is an application *)
let rec expansive { e_desc = desc } =
  match desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> false
    | Etuple(e_list) -> List.exists expansive e_list
    | Erecord(l_e_list) -> List.exists (fun (_, e) -> expansive e) l_e_list
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> expansive e
    | Erecord_with(e, l_e_list) ->
       expansive e || List.exists (fun (_, e) -> expansive e) l_e_list
    | _ -> true

let check_statefull loc expected_k =
  if not (Types.is_statefull_kind expected_k)
  then error loc Ekind_not_combinatorial

(** The type of states in automata *)
(** We emit a warning when a state is entered both by reset and history *)
type state = { mutable s_reset: bool option; s_parameters: typ list }

let check_target_state loc expected_reset actual_reset =
  match expected_reset with
    | None -> Some(actual_reset)
    | Some(expected_reset) ->
        if expected_reset <> actual_reset then
          warning loc (Wreset_target_state(actual_reset, expected_reset));
        Some(expected_reset)

(* Every shared variable defined in the initial state of an automaton *)
(* left weakly is considered to be an initialized state variable. *)
let turn_vars_into_memories h { dv = dv } =
  let add n acc =
    let ({ t_sort = sort; t_typ = typ } as tentry) = Env.find n h in
    match sort with
    | Smem({ m_init = Noinit } as m) ->
       Env.add n { tentry with t_sort = Smem { m with m_init = InitEq } } acc
    | Sstatic | Sval | Svar _ | Smem _ -> acc  in
  let first_h = S.fold add dv Env.empty in
  first_h, Env.append first_h h

(** Typing immediate values *)
let immediate = function
  | Ebool _ -> Initial.typ_bool
  | Eint(i) -> Initial.typ_int
  | Efloat(i) -> Initial.typ_float
  | Echar(c) -> Initial.typ_char
  | Estring(c) -> Initial.typ_string
  | Evoid -> Initial.typ_unit

(* once all branch of the automaton has been typed *)
(* incorporate the information computed about variables from *)
(* the initial environment into the global one *)
let incorporate_into_env first_h h =
  let mark n { t_sort = sort } =
    let tentry = Env.find n h in
    match sort with
    | Smem({ m_init = InitEq } as m) ->
       tentry.t_sort <- Smem { m with m_init = Noinit }
    | _ -> () in
  Env.iter mark first_h

(** Variables in a pattern *)
let vars pat = Vars.fv_pat S.empty S.empty pat

(** Types for local identifiers *)
let var loc h n =
  try Env.find n h
  with Not_found -> error loc (Evar_undefined(n))

let typ_of_var loc h n = let { t_typ = typ } = var loc h n in typ

(* Typing [last n] *)
let last loc h n =
  let { t_sort = sort; t_typ = typ } as entry = var loc h n in
  (* [last n] is allowed only if [n] is a state variable *)
  begin match sort with
  | Sstatic | Sval | Svar _ | Smem { m_next = Some(true) } ->
			       error loc (Elast_forbidden(n))
  | Smem (m) ->
     entry.t_sort <- Smem { m with m_previous = true }
  end; typ

(* Typing [der n = ...] *)
let derivative loc h n =
  let { t_typ = typ; t_sort = sort } as entry = var loc h n in
  (* [der n] is allowed only if [n] is a state variable *)
  match sort with
  | Sstatic | Sval | Svar _ ->
		      error loc (Eder_forbidden(n))
  | Smem(m) -> entry.t_sort <- Smem { m with m_kind = Some(Cont) }; typ

(* Typing [n += ...] *)
let pluseq loc h n =
  (* check that a name [n] is declared with a combination function *)
  let ({ t_typ = typ; t_sort = sort } as entry) = var loc h n in
  match sort with
  | Svar { v_combine = Some _ } -> typ
  | Sstatic | Sval | Svar { v_combine = None } | Smem { m_combine = None } ->
     error loc (Ecombination_function(n))
  | Smem ({ m_next = n_opt } as m) ->
     match n_opt with
     | None -> entry.t_sort <- Smem { m with m_next = Some(false) }; typ
     | Some(false) -> typ
     | Some(true) -> error loc (Ealready_with_different_kinds(Next, Multi, n))

(* Typing [init n = ...] *)
let init loc h n =
  (* set that [n] is initialized if it is not already at the definition point *)
  let { t_typ = typ; t_sort = sort } as entry = var loc h n in
  match sort with
  | Sstatic | Sval | Svar _ -> assert false
  | Smem ({ m_init = i } as m) ->
     match i with
     | Noinit -> entry.t_sort <- Smem { m with m_init = InitEq }; typ
     | InitEq -> typ
     | InitDecl _ -> error loc (Ealready(Initial, n))

(* Typing [next n = ...] *)
let next loc h n =
  let { t_typ = typ; t_sort = sort } as entry = var loc h n in
  match sort with
  | Sstatic | Sval | Svar _ -> assert false
  | Smem { m_previous = true } -> error loc (Enext_forbidden(n))
  | Smem ({ m_next = n_opt } as m) ->
     match n_opt with
     | None -> entry.t_sort <- Smem { m with m_next = Some(true) }; typ
     | Some(true) -> typ
     | Some(false) ->
        error loc (Ealready_with_different_kinds(Current, Next, n))

(* Typing [n = ...] *)
let def loc h n =
  let { t_sort = sort } as entry = var loc h n in
  match sort with
  | Sstatic | Sval | Svar _ -> ()
  | Smem ({ m_next = n_opt } as m) ->
     match n_opt with
     | None -> entry.t_sort <- Smem { m with m_next = Some(false) }
     | Some(false) -> ()
     | Some(true) ->
        error loc (Ealready_with_different_kinds(Next, Current, n))

(** Types for global identifiers *)
let global loc expected_k lname =
  let { qualid = qualid;
        info = { value_static = is_static;
                 value_typ = tys } } = find_value loc lname in
  less_than loc (if is_static then Tstatic true else expected_k) expected_k;
  qualid, Types.instance_of_type tys

let global_with_instance loc expected_k lname =
  let { qualid = qualid;
        info = { value_static = is_static;
                 value_typ = tys } } = find_value loc lname in
  less_than loc (if is_static then Tstatic true else expected_k) expected_k;
  let typ_instance, typ_body = Types.instance_and_vars_of_type tys in
  qualid, typ_instance, typ_body

let label loc l =
  let { qualid = qualid; info = tys_label } = find_label loc l in
  qualid, Types.label_instance tys_label

let constr loc c =
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

(** Check that every declared name is associated to a *)
(** defining equation and that an initialized state variable is *)
(** not initialized again in the body *)
(** Returns a new [defined_names] where names from [n_list] *)
(** have been removed *)
let check_definitions_for_every_name defined_names n_list =
  List.fold_left
    (fun { dv = dv; di = di; der = der; nv = nv; mv = mv }
      { vardec_name = n; vardec_default = d_opt; vardec_loc = loc } ->
     let in_dv = S.mem n dv in
     let in_di = S.mem n di in
     let in_der = S.mem n der in
     let in_nv = S.mem n nv in
     let in_mv = S.mem n mv in
     (* check that n is defined by an equation *)
     if not (in_dv || in_di || in_der || in_nv || in_mv)
     then error loc (Eequation_is_missing(n));
     (* remove local names *)
     { dv = if in_dv then S.remove n dv else dv;
       di = if in_di then S.remove n di else di;
       der = if in_der then S.remove n der else der;
       nv = if in_nv then S.remove n nv else nv;
       mv = if in_mv then S.remove n mv else mv })
    defined_names n_list

(** Typing a declaration *)

(* type checking of the combination function *)
let combine loc expected_ty lname  =
  let { qualid = qualid; info = { value_typ = tys } } =
    find_value loc lname in
  let ty = Types.instance_of_type tys in
  (* Its signature must be [expected_ty * expected_ty -A-> expected_ty] *)
  let ty_combine = Types.type_of_combine () in
  unify loc ty_combine ty

(* type checking of the declared default/init value *)
let constant loc expected_k expected_ty = function
  | Cimmediate(i) ->
     let actual_ty = immediate(i) in
     unify loc expected_ty actual_ty
  | Cglobal(lname) ->
     let qualid, actual_ty = global loc expected_k lname in
     unify loc expected_ty actual_ty

(* Typing the declaration of variables. The result is a typing environment *)
(* [inames] is the set of initialized variables, that is, variable *)
(* which appear in an [init x = e] equation *)
let vardec_list expected_k n_list inames =
  let default loc expected_ty c_opt = function
  | Init(v) ->
     (* the initialization must appear in a statefull function *)
     if not (Types.is_statefull_kind expected_k)
     then error loc Ekind_not_combinatorial;
     constant loc expected_k expected_ty v;
     Deftypes.Smem
       (Deftypes.cmem c_opt { empty_mem with m_init = InitDecl(v) })
  | Default(v) ->
     constant loc expected_k expected_ty v;
     Deftypes.default (Some(v)) c_opt in
  (* typing every declaration *)
  let vardec h0
             { vardec_name = n; vardec_default = d_opt; vardec_combine = c_opt;
               vardec_loc = loc } =
    let expected_ty = Types.new_var () in
    Misc.optional_unit (combine loc) expected_ty c_opt;
    let sort =
      match d_opt with
      | Some(d) -> default loc expected_ty c_opt d
      | None ->
         match expected_k with
         | Tstatic _ -> Deftypes.static
         | Tany | Tdiscrete false -> Deftypes.default None c_opt
         | Tdiscrete true
         | Tcont 
         | Tproba ->
	    Deftypes.Smem (Deftypes.cmem c_opt
                                         (if S.mem n inames then Deftypes.imem
                                          else Deftypes.empty_mem)) in
    Env.add n { t_typ = expected_ty; t_sort = sort } h0 in
  List.fold_left vardec Env.empty n_list

(** Computes the set of names defined in a list of definitions *)
let rec build (names, inames) { eq_desc = desc } =
  (* block *)
  let block_with_bounded (names, inames)
			 { b_vars = b_vars; b_body = eq_list } =
    let vardec acc { vardec_name = n } = S.add n acc in
    let bounded = List.fold_left vardec S.empty b_vars in
    let (local_names, local_inames) = build_list (S.empty, S.empty) eq_list in
    bounded, (S.union names (S.diff local_names bounded),
              S.union inames (S.diff local_inames bounded)) in
  let block (names, inames) b = snd (block_with_bounded (names, inames) b) in
  match desc with
  | EQeq(p, _) -> Vars.fv_pat S.empty names p, inames
  | EQder(n, _, _, _)
  | EQpluseq(n, _) | EQnext(n, _, _)
  | EQemit(n, _) -> S.add n names, inames
  | EQinit(n, _) -> S.add n names, S.add n inames
  | EQreset(eq_list, _)
  | EQand(eq_list)
  | EQbefore(eq_list) -> build_list (names, inames) eq_list
  | EQblock(b) -> block (names, inames) b
  | EQpresent(ph_list, b_opt) ->
     (* present handler *)
     let handler (names, inames) { p_body = b } = block (names, inames) b in
     let names, inames =
       List.fold_left handler (names, inames) ph_list in
     Misc.optional block (names, inames) b_opt
  | EQmatch(_, _, mh_list) ->
     (* match handler *)
     let handler (names, inames) { m_body = b } = block (names, inames) b in
     List.fold_left handler (names, inames) mh_list
  | EQautomaton(is_weak, sh_list, _) ->
     (* escape handler *)
     let escape (names, inames) { e_block = b_opt } =
       Misc.optional block (names, inames) b_opt in
     (* automaton handler *)
     let handler (names, inames) { s_body = b; s_trans = esc_list } =
       let bounded, (names, inames) =
         block_with_bounded (names, inames) b in
       let esc_names, esc_inames =
         List.fold_left escape (names, inames) esc_list in
       S.union names (if is_weak then S.diff esc_names bounded else esc_names),
       S.union inames
         (if is_weak then S.diff esc_inames bounded else esc_inames)
     in
     List.fold_left handler (names, inames) sh_list
  | EQforall { for_index = in_list; for_init = init_list } ->
     let index (names, inames) { desc = desc } =
       match desc with
       | Einput _ | Eindex _ -> names, inames
       | Eoutput(_, n) -> S.add n names, inames in
     let init (names, inames) { desc = desc } =
       match desc with
       | Einit_last(n, _) -> S.add n names, inames in
     let names, inames = List.fold_left index (names, inames) in_list in
     List.fold_left init (names, inames) init_list

and build_list (names, inames) eq_list =
  List.fold_left build (names, inames) eq_list

let env_of_eq_list expected_k eq_list =
  let names, inames = build_list (S.empty, S.empty) eq_list in
  S.fold
    (fun n acc ->
     let sort =
       match expected_k with
       | Deftypes.Tstatic _ -> Deftypes.static
       | Deftypes.Tany | Deftypes.Tdiscrete false -> Deftypes.variable
       | Deftypes. Tcont
       | Deftypes.Tdiscrete true
       | Deftypes.Tproba ->
	  if S.mem n inames then Deftypes.imemory
          else Deftypes.Smem (Deftypes.empty_mem) in
     Env.add n { t_typ = Types.new_var (); t_sort = sort } acc) names Env.empty

(* introduce a variable with the proper kind *)
(* [last x] is only be possible when [expected_k] is statefull *)
let intro_sort_of_var expected_k =
  match expected_k with
  | Deftypes.Tstatic _ -> Deftypes.static
  | Deftypes.Tany | Deftypes.Tdiscrete false -> Deftypes.Sval
  | Deftypes. Tcont
  | Deftypes.Tdiscrete true
  | Deftypes.Tproba -> Deftypes.Smem (Deftypes.empty_mem)

let env_of_scondpat expected_k scpat =
  let rec env_of acc { desc = desc } =
    match desc with
    | Econdand(sc1, sc2) -> env_of (env_of acc sc1) sc2
    | Econdor(sc, _) | Econdon(sc, _) -> env_of acc sc
    | Econdexp _ -> acc
    | Econdpat(_, pat) -> Vars.fv_pat S.empty acc pat in
  let acc = env_of S.empty scpat in
  S.fold
    (fun n acc ->
      Env.add n
        { t_typ = Types.new_var (); t_sort = intro_sort_of_var expected_k } acc)
         acc Env.empty

let env_of_statepat expected_k spat =
  let rec env_of acc { desc = desc } =
    match desc with
    | Estate0pat _ -> acc
    | Estate1pat(_, l) -> List.fold_left (fun acc n -> S.add n acc) acc l in
  let acc = env_of S.empty spat in
  S.fold
    (fun n acc ->
      Env.add n
        { t_typ = Types.new_var (); t_sort = intro_sort_of_var expected_k } acc)
         acc Env.empty

let env_of_pattern expected_k h0 pat =
  let acc = Vars.fv_pat S.empty S.empty pat in
  S.fold
    (fun n acc ->
      Env.add n
        { t_typ = Types.new_var (); t_sort = intro_sort_of_var expected_k } acc)
    acc h0

(* the [n-1] first arguments are static. If [expected_k] is static *)
(* the last one too *)
let env_of_pattern_list expected_k env p_list =
  let p_list, p = Misc.firsts p_list in
  let env = List.fold_left (env_of_pattern (Deftypes.Tstatic true)) env p_list in
  env_of_pattern expected_k env p

let env_of_pattern expected_k pat = env_of_pattern expected_k Env.empty pat

(** Typing patterns *)
(* the kind of variables in [p] must be equal to [expected_k] *)
let rec pattern h ({ p_desc = desc; p_loc = loc } as pat) ty =
  match desc with
  | Ewildpat ->
     (* type annotation *)
     pat.p_typ <- ty
  | Econstpat(im) ->
     unify_pat pat ty (immediate im);
     (* type annotation *)
     pat.p_typ <- ty
  | Econstr0pat(c0) ->
     let qualid, { constr_res = ty_res; constr_arity = n } = constr loc c0 in
     (* check the arity *)
     if n <> 0 then error loc (Econstr_arity(c0, n, 0));
     unify_pat pat ty ty_res;
     pat.p_desc <- Econstr0pat(Lident.Modname(qualid));
     (* type annotation *)
     pat.p_typ <- ty
  | Econstr1pat(c1, pat_list) ->
     let qualid,
         { constr_arg = ty_list; constr_res = ty_res; constr_arity = n } =
       constr loc c1 in
     (* check the arity *)
     let actual_n = List.length pat_list in
     if n <> actual_n then error loc (Econstr_arity(c1, n, actual_n));
     unify_pat pat ty ty_res;
     pat.p_desc <- Econstr1pat(Lident.Modname(qualid), pat_list);
     (* type annotation *)
     pat.p_typ <- ty;
     List.iter2 (pattern h) pat_list ty_list
  | Evarpat(x) ->
     unify_pat pat ty (typ_of_var loc h x);
     (* type annotation *)
     pat.p_typ <- ty
  | Etuplepat(pat_list) ->
     let ty_list = List.map (fun _ -> new_var ()) pat_list in
     unify_pat pat ty (product ty_list);
     (* type annotation *)
     pat.p_typ <- ty;
     List.iter2 (pattern h) pat_list ty_list
  | Etypeconstraintpat(p, typ_expr) ->
     let expected_typ =
       Types.instance_of_type(Interface.scheme_of_type typ_expr) in
     unify_pat pat expected_typ ty;
     (* type annotation *)
     pat.p_typ <- ty;
     pattern h p ty
  | Erecordpat(label_pat_list) ->
     (* type annotation *)
     pat.p_typ <- ty;
     let label_pat_list =
       List.map
         (fun (lab, pat_label) ->
          let qualid, { label_arg = ty_arg; label_res = ty_res } =
            label pat.p_loc lab in
          unify_pat pat_label ty ty_arg;
          pattern h pat_label ty_res;
          Lident.Modname(qualid), pat_label) label_pat_list in
     pat.p_desc <- Erecordpat(label_pat_list)
  | Ealiaspat(p, x) ->
     unify_pat pat ty (typ_of_var loc h x);
     (* type annotation *)
     pat.p_typ <- ty;
     pattern h p ty
  | Eorpat(p1, p2) ->
     (* type annotation *)
     pat.p_typ <- ty;
     pattern h p1 ty;
     pattern h p2 ty

(* typing a list of patterns. The first [n-1] patterns define static *)
(* values; the [n]-th one has no constraint *)
let pattern_list h pat_list ty_list = List.iter2 (pattern h) pat_list ty_list

(* check that a pattern is total *)
let check_total_pattern p =
  let is_exhaustive = Patternsig.check_activate p.p_loc p in
  if not is_exhaustive then error p.p_loc Epattern_not_total

let check_total_pattern_list p_list = List.iter check_total_pattern p_list

(** Typing a pattern matching. Returns defined names *)
let match_handlers body loc expected_k h total m_handlers pat_ty ty =
  let handler ({ m_pat = pat; m_body = b } as mh) =
    let h0 = env_of_pattern expected_k pat in
    pattern h0 pat pat_ty;
    mh.m_env <- h0;
    let h = Env.append h0 h in
    body expected_k h b ty in
  let defined_names_list = List.map handler m_handlers in
  (* check partiality/redundancy of the pattern matching *)

  let is_exhaustive =
    !total || (Patternsig.check_match_handlers loc m_handlers) in

  let defined_names_list =
    if is_exhaustive then defined_names_list
    else Deftypes.empty :: defined_names_list in
  (* set total to the right value *)
  total := is_exhaustive;
  (* identify variables which are defined partially *)
  Total.merge loc h defined_names_list

(** Typing a present handler. Returns defined names *)
(** for every branch the expected kind is discrete. For the default case *)
(** it is the kind of the context. *)
let present_handlers scondpat body loc expected_k h p_h_list b_opt expected_ty =
  let handler ({ p_cond = scpat; p_body = b } as ph) =
    (* local variables from [scpat] cannot be accessed through a last *)
    let h0 = env_of_scondpat expected_k scpat in
    let h = Env.append h0 h in
    let is_zero = Types.is_continuous_kind expected_k in
    scondpat expected_k is_zero h scpat;
    (* sets [zero = true] is [expected_k = Tcont] *)
    ph.p_zero <- is_zero;
    ph.p_env <- h0;
    body (Types.lift_to_discrete expected_k) h b expected_ty in

  let defined_names_list = List.map handler p_h_list in

  (* treat the optional default case *)
  let defined_names_list =
    match b_opt with
    | None -> Deftypes.empty :: defined_names_list
      | Some(b) -> let defined_names = body expected_k h b expected_ty in
          defined_names :: defined_names_list in

  (* identify variables which are defined partially *)
  Total.merge loc h defined_names_list


(* [expression expected_k h e] returns the type for [e] *)
let rec expression expected_k h ({ e_desc = desc; e_loc = loc } as e) =
  let ty = match desc with
    | Econst(i) -> immediate i
    | Elocal(x) ->
        let { t_typ = typ; t_sort = sort } = var loc h x in
        sort_less_than loc sort expected_k;
        typ
    | Eglobal { lname = lname } ->
        let qualid, typ_instance, ty =
          global_with_instance loc expected_k lname in
        e.e_desc <- Eglobal { lname = Lident.Modname(qualid);
                              typ_instance = typ_instance }; ty
    | Elast(x) -> last loc h x
    | Etuple(e_list) ->
        product (List.map (expression expected_k h) e_list)
    | Eop(Eaccess, [e1; e2]) ->
        (* Special typing for [e1.(e2)]. [e1] must be of type [ty[size]]  *)
        (* with [size] a known expression at that point *)
        let ty = expression expected_k h e1 in
        let ty_arg, _ = check_is_vec e1.e_loc ty in
        expect expected_k h e2 Initial.typ_int; ty_arg
    | Eop(Eupdate, [e1; i; e2]) ->
        (* Special typing for [{ e1 with (i) = e2 }]. *)
        (* [e1] must be of type [ty[size]]  *)
        (* with [size] a known expression at that point *)
        let ty = expression expected_k h e1 in
        let ty_arg,_ = check_is_vec e1.e_loc ty in
        expect expected_k h i Initial.typ_int;
        expect expected_k h e2 ty_arg; ty
    | Eop(Eslice(s1, s2), [e]) ->
        (* Special typing for [e{ e1 .. e2}] *)
        (* [e1] and [e2] must be size expressions *)
        let s1 = size h s1 in
        let s2 = size h s2 in
        let ty = expression expected_k h e in
        let ty_arg, _ = check_is_vec e.e_loc ty in
        Types.vec ty_arg (Types.plus (Types.minus s2 s1) (Types.const 1))
    | Eop(Econcat, [e1; e2]) ->
        let ty1 = expression expected_k h e1 in
        let ty_arg1, s1 = check_is_vec e1.e_loc ty1 in
        let ty2 = expression expected_k h e2 in
        let ty_arg2, s2 = check_is_vec e2.e_loc ty2 in
        unify_expr e2 ty_arg1 ty_arg2;
        Types.vec ty_arg1 (Types.plus s1 s2)
    | Eop(op, e_list) ->
        operator expected_k h loc op e_list
    | Eapp({ app_statefull = is_statefull }, e, e_list) ->
        apply loc is_statefull expected_k h e e_list
    | Econstr0(c0) ->
        let qualid, { constr_res = ty_res; constr_arity = n } =
          constr loc c0 in
        if n <> 0 then error loc (Econstr_arity(c0, n, 0));
        e.e_desc <- Econstr0(Lident.Modname(qualid)); ty_res
    | Econstr1(c1, e_list) ->
        let qualid,
            { constr_arg = ty_list; constr_res = ty_res; constr_arity = n } =
          constr loc c1 in
        let actual_arity = List.length e_list in
        if n <> actual_arity then
          error loc (Econstr_arity(c1, n, actual_arity));
        List.iter2 (expect expected_k h) e_list ty_list;
        e.e_desc <- Econstr1(Lident.Modname(qualid), e_list); ty_res
    | Erecord_access(e1, lab) ->
        let qualid, { label_arg = ty_arg; label_res = ty_res } =
          label loc lab in
        expect expected_k h e1 ty_arg;
        e.e_desc <- Erecord_access(e1, Lident.Modname(qualid)); ty_res
    | Erecord(label_e_list) ->
        let ty = new_var () in
        let label_e_list =
          List.map
            (fun (lab, e_label) ->
               let qualid, { label_arg = ty_arg; label_res = ty_res } =
                 label loc lab in
               unify_expr e ty ty_arg;
               expect expected_k h e_label ty_res;
               (Lident.Modname(qualid), e_label)) label_e_list in
        e.e_desc <- Erecord(label_e_list);
        (* check that no field is missing *)
        let label_desc_list = get_all_labels loc ty in
        if List.length label_e_list <> List.length label_desc_list
        then error loc Esome_labels_are_missing;
        ty
    | Erecord_with(e1, label_e_list) ->
       let ty = new_var () in
        let label_e_list =
          List.map
            (fun (lab, e_label) ->
               let qualid, { label_arg = ty_arg; label_res = ty_res } =
                 label loc lab in
               unify_expr e ty ty_arg;
               expect expected_k h e_label ty_res;
               (Lident.Modname(qualid), e_label)) label_e_list in
	expect expected_k h e1 ty;
        e.e_desc <- Erecord_with(e1, label_e_list);
	ty
    | Etypeconstraint(exp, typ_expr) ->
        let expected_typ =
          Types.instance_of_type (Interface.scheme_of_type typ_expr) in
        expect expected_k h exp expected_typ;
        expected_typ
    | Elet(l, e) ->
        let h = local expected_k h l in
        expression expected_k h e
    | Eblock(b, e) ->
        let h, _ = block_eq_list expected_k h b in
        expression expected_k h e
    | Eseq(e1, e2) ->
        ignore (expression expected_k h e1);
        expression expected_k h e2
    | Eperiod(p) ->
        (* periods are only valid in a continuous context *)
        less_than loc Tcont expected_k;
        (* a period must be a static expression *)
        period (Tstatic(true)) h p;
        Types.zero_type expected_k
    | Ematch(total, e, m_h_list) ->
        let expected_pat_ty = expression expected_k h e in
        let expected_ty = new_var () in
        ignore
          (match_handler_exp_list
             loc expected_k h total m_h_list expected_pat_ty expected_ty);
        expected_ty
    | Epresent(p_h_list, e_opt) ->
        let expected_ty = new_var () in
        ignore
          (present_handler_exp_list loc expected_k h p_h_list e_opt expected_ty);
        expected_ty in
  (* check that ty belongs to kind expected_k *)
  type_is_in_kind loc expected_k ty;
  (* type annotation *)
  e.e_typ <- ty;
  ty

(** Typing a size expression *)
and size h { desc = desc; loc = loc } =
  match desc with
  | Sconst(i) -> Types.const i
  | Sglobal(ln) ->
      let qualid, _, typ_body = global_with_instance loc (Tstatic(true)) ln in
      unify loc Initial.typ_int typ_body;
      Types.global(qualid)
  | Sname(x) ->
      let { t_typ = typ; t_sort = sort } = var loc h x in
      sort_less_than loc sort (Tstatic(true));
      unify loc Initial.typ_int typ;
      Types.name x
  | Sop(Splus, s1, s2) ->
      let s1 = size h s1 in
      let s2 = size h s2 in
      Types.plus s1 s2
  | Sop(Sminus, s1, s2) ->
      let s1 = size h s1 in
      let s2 = size h s2 in
      Types.minus s1 s2


(** Convert an expression into a size expression *)
and size_of_exp { e_desc = desc; e_loc = loc } =
  match desc with
  | Econst(Eint(i)) -> Tconst(i)
  | Elocal(n) -> Tname(n)
  | Eglobal { lname = Lident.Modname(qualid) } -> Tglobal(qualid)
  | Eapp(_, { e_desc = Eglobal { lname = Lident.Modname(qualid) } }, [e1; e2])
    when qualid = Initial.stdlib_name "+" ->
      Top(Tplus, size_of_exp e1, size_of_exp e2)
  | Eapp(_, { e_desc = Eglobal { lname = Lident.Modname(qualid) } }, [e1; e2])
    when qualid = Initial.stdlib_name "-" ->
      Top(Tminus, size_of_exp e1, size_of_exp e2)
  | _ -> error loc Enot_a_size_expression

(** The type of primitives and imported functions *)
and operator expected_k h loc op e_list =
  let actual_k, ty_args, ty_res =
    match op with
    | Eifthenelse ->
        let ty = new_var () in
        Tany, [Initial.typ_bool; ty; ty], ty
    | Eunarypre ->
        let ty = new_var () in
        Tdiscrete(true), [ty], ty
    | (Eminusgreater | Efby) ->
        let ty = new_var () in
        Tdiscrete(true), [ty; ty], ty
    | (Eup | Ehorizon) ->
        Tcont, [Initial.typ_float], Initial.typ_zero
    | Etest ->
        let ty = new_var () in
        Tany, [Initial.typ_signal ty], Initial.typ_bool
    | Edisc ->
        let ty = new_var () in
        Tcont, [ty], Initial.typ_zero
    | Einitial ->
        Tcont, [], Initial.typ_zero
    | Eatomic ->
        let ty = new_var () in
        expected_k, [ty], ty
    | Eaccess | Eupdate | Eslice _ | Econcat -> assert false in
  less_than loc actual_k expected_k;
  List.iter2 (expect expected_k h) e_list ty_args;
  ty_res


and period expected_k h { p_phase = p1_opt; p_period = p2 } =
  expect expected_k h p2 Initial.typ_float;
  match p1_opt with None -> () | Some(p1) -> expect expected_k h p1 Initial.typ_float

(** Typing an expression with expected type [expected_type] *)
and expect expected_k h e expected_ty =
  let actual_ty = expression expected_k h e in
  unify_expr e expected_ty actual_ty

and apply loc is_statefull expected_k h e arg_list =
  (* the function [e] must be static *)
  let ty_fct = expression (Tstatic(true)) h e in
  (* [run f e] forces [f] to be of type [t1 -expected_k-> t2] *)
  (* and [k] to be either [D] or [C] *)
  if is_statefull then
    begin
      check_statefull loc expected_k;
      unify_expr e (Types.run_type expected_k) ty_fct
    end;
  let intro_k = Types.intro expected_k in
  (* typing the list of arguments *)
  (* the [n-1] arguments must be static; the [nth] is of kind [expected_k] *)
  let rec args ty_fct = function
    | [] -> ty_fct
    | arg :: arg_list ->
       let actual_k, n_opt, ty1, ty2 =
         try Types.filter_arrow intro_k ty_fct
         with Unify ->  error loc (Eapplication_of_non_function) in
       let expected_k = lift loc expected_k actual_k in
       expect expected_k h arg ty1;
       let ty2 =
         match n_opt with
         | None -> ty2
         | Some(n) -> subst_in_type (Env.singleton n (size_of_exp arg)) ty2 in
       args ty2 arg_list in
  args ty_fct arg_list

(** Typing an equation. Returns the set of defined names *)
and equation expected_k h ({ eq_desc = desc; eq_loc = loc } as eq) =
  let defnames = match desc with
    | EQeq(p, e) ->
        let ty_e = expression expected_k h e in
        pattern h p ty_e;
        (* check that the pattern is total *)
        check_total_pattern p;
        let dv = vars p in
        S.iter (def loc h) dv;
        { Deftypes.empty with dv = dv }
    | EQpluseq(n, e) ->
        let actual_ty = expression expected_k h e in
        let expected_ty = pluseq loc h n in
        unify loc expected_ty actual_ty;
        { Deftypes.empty with mv = S.singleton n }
    | EQinit(n, e0) ->
        (* an initialization is valid only in a continuous or discrete context *)
        check_statefull loc expected_k;
        let actual_ty = init loc h n in
        expect (Types.lift_to_discrete expected_k) h e0 actual_ty;
        (* sets that every variable from [di] is initialized *)
        { Deftypes.empty with di = S.singleton n }
    | EQnext(n, e, e0_opt) ->
        (* a next is valid only in a discrete context *)
        less_than loc (Tdiscrete(true)) expected_k;
        let actual_ty = next loc h n in
        expect expected_k h e actual_ty;
        let di =
          match e0_opt with
          | None -> S.empty
          | Some(e) ->
              expect expected_k h e actual_ty; ignore (init loc h n);
              S.singleton n
        in
        { Deftypes.empty with nv = S.singleton n; di = di }
    | EQder(n, e, e0_opt, p_h_e_list) ->
        (* integration is only valid in a continuous context *)
        less_than loc Tcont expected_k;
        let actual_ty = derivative loc h n in
        unify loc Initial.typ_float actual_ty;
        expect expected_k h e actual_ty;
        let di =
          match e0_opt with
          | None -> S.empty
          | Some(e) ->
             expect (Types.lift_to_discrete expected_k) h e Initial.typ_float;
             ignore (init loc h n); S.singleton n in
        ignore (present_handler_exp_list
                  loc expected_k h p_h_e_list None Initial.typ_float);
        { Deftypes.empty with di = di; der = S.singleton n }
    | EQautomaton(is_weak, s_h_list, se_opt) ->
        (* automata are only valid in continuous or discrete context *)
        check_statefull loc expected_k;
        automaton_handlers is_weak loc expected_k h s_h_list se_opt
    | EQmatch(total, e, m_h_list) ->
        let expected_pat_ty = expression expected_k h e in
        match_handler_block_eq_list
          loc expected_k h total m_h_list expected_pat_ty
    | EQpresent(p_h_list, b_opt) ->
        present_handler_block_eq_list loc expected_k h p_h_list b_opt
    | EQreset(eq_list, e) ->
        expect expected_k h e (Types.zero_type expected_k);
        equation_list expected_k h eq_list
    | EQand(eq_list)
    | EQbefore(eq_list) -> equation_list expected_k h eq_list
    | EQemit(n, e_opt) ->
        less_than loc expected_k (Types.lift_to_discrete expected_k);
        let ty_e = new_var () in
        let ty_name = typ_of_var loc h n in
        begin match e_opt with
            | None -> unify loc (Initial.typ_signal Initial.typ_unit) ty_name
            | Some(e) ->
                unify loc (Initial.typ_signal ty_e) ty_name;
                expect expected_k h e ty_e
        end;
        { Deftypes.empty with dv = S.singleton n }
    | EQblock(b_eq_list) ->
       snd (block_eq_list expected_k h b_eq_list)
    | EQforall
        ({ for_index = i_list; for_init = init_list; for_body = b_eq_list }
          as body) ->
        (* all output variables [xi] such that [xi ou x] *)
        (* must have a declaration in the body *)
        (* A non local variable [xi] defined in the body of the loop must be *)
        (* either declared in the initialization part [initialize ...] *)
        (* or used to define an output array [xi out x] *)
        (* returns a new set [{ dv; di; der; nv; mv }] *)
        (* where [xi] is replaced by [x] *)
        let merge ({ dv = dv; di = di; der = der; nv = nv; mv = mv } as defnames)
            h init_h out_h xi_out_x =
          (* check that all names in [out_h] are defined in defnames *)
          let out_set = Env.fold (fun x _ acc -> S.add x acc) out_h S.empty in
          let out_not_defined =
            S.diff out_set (Deftypes.names S.empty defnames) in
          if not (S.is_empty out_not_defined)
          then error loc (Eequation_is_missing(S.choose out_not_defined));
          (* rename [xi] into [x] if [xi out x] appears in [xi_out_x] *)
          let x_of_xi xi =
            try Env.find xi xi_out_x  with Not_found -> xi in
          let out xi acc =
            try S.add (Env.find xi xi_out_x) acc with Not_found -> acc in
          (* all variables in [dv], [der] must appear either *)
          (* in [init_h] or [out_h] or as combined variables in [h] *)
          (* all variables in [di] must appear in [out_h] and not in [init_h] *)
          let belong_to_init_out xi =
            if not ((Env.mem xi init_h) || (Env.mem xi out_h))
            then error loc (Ealready_in_forall(xi)) in
          let belong_to_out_not_init xi =
            if not (Env.mem xi out_h) || (Env.mem xi init_h)
            then error loc (Ealready_in_forall(xi)) in
            S.iter belong_to_init_out dv;
            S.iter belong_to_init_out nv;
            S.iter belong_to_init_out der;
            S.iter belong_to_out_not_init di;
            (* change the sort of [x] so that it is equal to that of [xi] *)
            S.iter (def loc h) (S.fold out dv S.empty);
            S.iter (fun n -> ignore (init loc h n)) (S.fold out di S.empty);
            S.iter
              (fun n -> ignore (derivative loc h n)) (S.fold out der S.empty);

          (* all name [xi] from [defnames] such that [xi out x] *)
          (* is replaced by [x] in the new [defnames] *)
          { dv = S.map x_of_xi dv; di = S.map x_of_xi di;
            der = S.map x_of_xi der; nv = S.map x_of_xi nv;
            mv = S.map x_of_xi mv } in

       (* outputs are either shared or state variables *)
       let sort = if Types.is_statefull_kind expected_k
                  then Deftypes.Smem Deftypes.empty_mem
                  else Deftypes.variable in

       (* bounds for loops must be static *)
       (* computes the set of array names returned by the loop *)
       (* declarations are red from left to right. For [i in e0..e1], *)
       (* compute the size [(e1 - e0) + 1)] for the arrays *)
       let index (in_h, out_h, xi_out_x, size_opt)
                 { desc = desc; loc = loc } =
         let size_of loc size_opt =
           match size_opt with
           | None -> error loc Esize_of_vec_is_undetermined
           | Some(actual_size) -> actual_size in
         match desc with
         | Einput(xi, e) ->
            let ty = Types.new_var () in
            let si = size_of loc size_opt in
            expect Tany h e (Types.vec ty si);
            Env.add xi { t_typ = ty; t_sort = Sval } in_h,
            out_h, xi_out_x, size_opt
         | Eoutput(xi, x) ->
            let ty_xi = Types.new_var () in
            let ty_x = typ_of_var loc h x in
            let si = size_of loc size_opt in
            unify loc (Types.vec ty_xi si) ty_x;
            in_h, Env.add xi { t_typ = ty_xi; t_sort = sort } out_h,
            Env.add xi x xi_out_x, size_opt
         | Eindex(i, e0, e1) ->
            expect (Tstatic(true)) h e0 Initial.typ_int;
            expect (Tstatic(true)) h e1 Initial.typ_int;
            (* check that the size [(e1 - e0) + 1)] is the same for *)
            (* all indices *)
            let e0 = size_of_exp e0 in
            let e1 = size_of_exp e1 in
            let actual_size =
              Types.plus (Types.minus e1 e0) (Types.const 1) in
            let size_opt =
              match size_opt with
                | None -> Some(actual_size)
                | Some(expected_size) ->
                  equal_sizes loc expected_size actual_size; size_opt in
            Env.add i { t_typ = Initial.typ_int; t_sort = Sval } in_h,
            out_h, xi_out_x, size_opt in

       (* returns the set of names defined by the loop body *)
       let init init_h { desc = desc; loc = loc } =
         match desc with
         | Einit_last(i, e) ->
            let ty = typ_of_var loc h i in
            expect expected_k h e ty;
            Env.add i { t_typ = ty; t_sort = Deftypes.memory } init_h in
       let init_h = List.fold_left init Env.empty init_list in

       let in_h, out_h, xi_out_x, _ =
         List.fold_left index (Env.empty, Env.empty, Env.empty, None) i_list in
       body.for_in_env <- in_h;
       body.for_out_env <- out_h;

       (* the environment [h] is extended with [in_h], [out_h] and [init_h] *)
       let h_eq_list =
         Env.append in_h (Env.append out_h (Env.append init_h h)) in
       let _, defnames =
         block_eq_list expected_k h_eq_list b_eq_list in
       (* check that every name in defnames is either declared *)
       (* in the initialize branch, an output or a multi-emitted value *)
       merge defnames h init_h out_h xi_out_x in
  (* set the names defined in the current equation *)
  eq.eq_write <- defnames;
  (* every equation must define at least a name *)
  (* if S.is_empty (Deftypes.names S.empty defnames) *)
  (* then warning loc Wequation_does_not_define_a_name; *)
  defnames

and equation_list expected_k h eq_list =
  List.fold_left
    (fun defined_names eq ->
      Total.join eq.eq_loc (equation expected_k h eq) defined_names)
    Deftypes.empty eq_list

(** Type a present handler when the body is an expression *)
and present_handler_exp_list loc expected_k h p_h_list e0_opt expected_ty =
  present_handlers scondpat
    (fun expected_k h e expected_ty ->
      expect expected_k h e expected_ty; Deftypes.empty)
    loc expected_k h p_h_list e0_opt expected_ty

and present_handler_block_eq_list loc expected_k h p_h_list b_opt =
  present_handlers scondpat
    (fun expected_k h b _ -> snd (block_eq_list expected_k h b))
    loc expected_k h p_h_list b_opt Initial.typ_unit

and match_handler_block_eq_list loc expected_k h total m_h_list pat_ty =
  match_handlers
    (fun expected_k h b _ -> snd (block_eq_list expected_k h b))
    loc expected_k h total m_h_list pat_ty Initial.typ_unit

and match_handler_exp_list loc expected_k h total m_h_list pat_ty ty =
  match_handlers
    (fun expected_k h e expected_ty ->
      expect expected_k h e expected_ty; Deftypes.empty)
    loc expected_k h total m_h_list pat_ty ty

and block_eq_list expected_k h
                  ({ b_vars = n_list; b_locals = l_list;
                     b_body = eq_list } as b) =
  (* initialize the local environment *)
  let _, inames = build_list (S.empty, S.empty) eq_list in
  let h0 = vardec_list expected_k n_list inames in
  let h = Env.append h0 h in
  let new_h = List.fold_left (local expected_k) h l_list in
  let defined_names = equation_list expected_k new_h eq_list in
  (* check that every local variable from [l_list] appears in *)
  (* [defined_variable] and that initialized state variables are not *)
  (* re-initialized in the body *)
  let defined_names =
    check_definitions_for_every_name defined_names n_list in
  (* annotate the block with the set of written variables and environment *)
  b.b_write <- defined_names;
  b.b_env <- h0;
  new_h, defined_names

and local expected_k h ({ l_eq = eq_list } as l) =
  (* decide whether [last x] is allowed or not on every [x] from [h0] *)
  let h0 = env_of_eq_list expected_k eq_list in
  l.l_env <- h0;
  let new_h = Env.append h0 h in
  ignore (equation_list expected_k new_h eq_list);
  Env.append h0 h

(** Typing a signal condition *)
(* when [is_zero_type = true], [scpat] must be either of type          *)
(* [zero] or [t signal]. [h] is the typing environment                 *)
(* Under a kind [k = Any], [sc on e] is correct if [e] is of kind [AD] *)
(* The reason is that the possible discontinuity of [e] only effect    *)
(* when [sc] is true *)
and scondpat expected_k is_zero_type h scpat =
  let rec typrec expected_k is_zero_type scpat =
    match scpat.desc with
      | Econdand(sc1, sc2) ->
          typrec expected_k is_zero_type sc1;
          typrec expected_k is_zero_type sc2
      | Econdor(sc1, sc2) ->
          typrec expected_k is_zero_type sc1;
          typrec expected_k is_zero_type sc2
      | Econdexp(e) ->
          let expected_ty =
            if is_zero_type then Initial.typ_zero else Initial.typ_bool in
          ignore (expect expected_k h e  expected_ty)
      | Econdpat(e_cond, pat) ->
          (* check that e is a signal *)
          let ty = new_var () in
          ignore (expect expected_k h e_cond (Initial.typ_signal ty));
          pattern h pat ty
      | Econdon(sc1, e) ->
          typrec expected_k is_zero_type sc1;
          ignore
            (expect (Types.on_type expected_k) h e Initial.typ_bool)
  in
  typrec expected_k is_zero_type scpat


(* typing state expressions. [state] must be a stateless expression *)
(* [actual_reset = true] if [state] is entered by reset *)
and typing_state h def_states actual_reset state =
  match state.desc with
    | Estate0(s) ->
        begin try
          let ({ s_reset = expected_reset; s_parameters = args } as r) =
            Env.find s def_states in
          if args <> []
          then error state.loc (Estate_arity_clash(s, 0, List.length args));
          r.s_reset <-
            check_target_state state.loc expected_reset actual_reset
        with
          | Not_found -> error state.loc (Estate_unbound s)
        end
    | Estate1(s, l) ->
        let ({ s_reset = expected_reset; s_parameters = args } as r) =
          try
            Env.find s def_states
          with
            | Not_found -> error state.loc (Estate_unbound s) in
        begin try
          List.iter2
            (fun e expected_ty -> ignore (expect Tany h e expected_ty))
            l args;
          r.s_reset <-
            check_target_state state.loc expected_reset actual_reset
        with
          | Invalid_argument _ ->
              error state.loc
                (Estate_arity_clash(s, List.length l, List.length args))
        end

(* Once the body of an automaton has been typed, indicate for every *)
(* handler if it is always entered by reset or not *)
and mark_reset_state def_states state_handlers =
  let mark ({ s_state = statepat } as handler) =
    let { s_reset = r } =
      Env.find (Total.Automaton.statepatname statepat) def_states in
    let v = match r with | None | Some(false) -> false | Some(true) -> true in
    handler.Zelus.s_reset <- v in
  List.iter mark state_handlers

(** Typing an automaton. Returns defined names *)
and automaton_handlers is_weak loc expected_k h state_handlers se_opt =
  (* check that all declared states are accessible *)
  Total.Automaton.check_all_states_are_accessible loc state_handlers;

  (* global table which associate the set of defined_names for every state *)
  let t = Total.Automaton.table state_handlers in

  (* build the environment of states. *)
  let addname acc { s_state = statepat } =
    match statepat.desc with
      | Estate0pat(s) -> Env.add s { s_reset = None; s_parameters = [] } acc
      | Estate1pat(s, l) ->
          Env.add s { s_reset = None;
                      s_parameters = (List.map (fun _ -> new_var ()) l)} acc in
  let def_states = List.fold_left addname Env.empty state_handlers in

  (* in case [se_opt = None], checks that the initial state is a non *)
  (* parameterised state. *)
  let { s_state = statepat } = List.hd state_handlers in
  begin match se_opt with
    | None ->
        begin match statepat.desc with
          | Estate1pat _ -> error statepat.loc Estate_initial
          | Estate0pat _ -> ()
        end
    | Some(se) -> typing_state h def_states true se
  end;

  (* the type for conditions on transitions *)
  let is_zero_type = Types.is_continuous_kind expected_k in

  (* typing the body of the automaton *)
  let typing_handler h
        ({ s_state = statepat; s_body = b; s_trans = trans } as s) =
    let escape source_state h expected_k
        ({ e_cond = scpat; e_reset = r; e_block = b_opt;
           e_next_state = state } as esc) =
      (* type one escape condition *)
      let h0 = env_of_scondpat expected_k scpat in
      let h = Env.append h0 h in
      scondpat expected_k is_zero_type h scpat;
      (* sets flag [zero = true] when [is_zero_type = true] *)
      esc.e_zero <- is_zero_type;
      esc.e_env <- h0;
      let h, defined_names =
        match b_opt with
          | None -> h, Deftypes.empty
          | Some(b) -> block_eq_list (Tdiscrete(true)) h b in
      (* checks that [state] belond to the current set of [states] *)
      typing_state h def_states r state;
      (* checks that names are not defined twice in a state *)
      let statename =
        if is_weak then source_state else Total.Automaton.statename state in
      Total.Automaton.add_transition is_weak h statename defined_names t in

    (* typing the state pattern *)
    let h0 = env_of_statepat expected_k statepat in
    s.s_env <- h0;
    begin match statepat.desc with
      | Estate0pat _ -> ()
      | Estate1pat(s, n_list) ->
          let { s_parameters = ty_list } = Env.find s def_states in
          List.iter2
            (fun n ty ->
             unify statepat.loc
                   (typ_of_var statepat.loc h0 n) ty) n_list ty_list;
    end;
    let h = Env.append h0 h in
    (* typing the body *)
    let new_h, defined_names = block_eq_list expected_k h b in
    (* add the list of defined_names to the current state *)
    let source_state = Total.Automaton.statepatname statepat in
    Total.Automaton.add_state source_state defined_names t;
    List.iter (escape source_state new_h expected_k) trans;
    defined_names in

  let first_handler = List.hd state_handlers in
  let remaining_handlers = List.tl state_handlers in

  (* first type the initial branch *)
  let defined_names = typing_handler h first_handler in
  (* if the initial state has only weak transition then all *)
  (* variables from [defined_names] do have a last value *)
  let first_h, new_h = if is_weak then turn_vars_into_memories h defined_names
                       else Env.empty, h in

  let defined_names_list =
    List.map (typing_handler new_h) remaining_handlers in

  (* identify variables which are partially defined in some states *)
  (* and/or transitions *)
  let defined_names = Total.Automaton.check loc new_h t in
  (* write defined_names in every handler *)
  List.iter2
    (fun { s_body = { b_write = _ } as b } defined_names ->
      b.b_write <- defined_names)
    state_handlers (defined_names :: defined_names_list);

  (* incorporate all the information computed concerning variables *)
  (* from the initial handler into the global one *)
  incorporate_into_env first_h h;

  (* finally, indicate for every state handler if it is entered *)
  (* by reset or not *)
  mark_reset_state def_states state_handlers;
  defined_names

(** Check that size variables are all bounded *)
let no_unbounded_name loc free_in_ty ty =
  if not (S.is_empty free_in_ty)
  then let n = S.choose free_in_ty in
       error loc (Esize_parameter_cannot_be_generalized(n, ty))
  else ty

(* make a function type from a function definition. *)
(* remove useless dependences:
 * - (n:ty_arg) -k-> ty_res => ty_arg -k-> ty_res if n not in fv_size(ty_res)
 * - if some name stay unbounded, raise an error *)
let funtype loc expected_k pat_list ty_list ty_res =
  let rec arg pat_list ty_list fv_in_ty_res =
    match pat_list, ty_list with
    | [], [] -> [], fv_in_ty_res
    | pat :: pat_list, ty_arg :: ty_list ->
       let ty_res_list, fv_in_ty_res =
         arg pat_list ty_list fv_in_ty_res in
       let fv_pat = Vars.fv_pat S.empty S.empty pat in
       let opt_name, fv_in_ty_res =
         let fv_inter = S.inter fv_pat fv_in_ty_res in
         if S.is_empty fv_inter then None, fv_in_ty_res
         else match pat.p_desc with
              | Evarpat(n) -> Some(n), S.remove n fv_in_ty_res
              | _ -> error pat.p_loc Esize_parameter_must_be_a_name in
       (opt_name, ty_arg) :: ty_res_list, fv fv_in_ty_res ty_arg
    | _ -> assert false in
  let ty_arg_list, fv_in_ty_res = arg pat_list ty_list (fv S.empty ty_res) in
  let ty_res = funtype_list expected_k ty_arg_list ty_res in
  no_unbounded_name loc fv_in_ty_res ty_res

(* The main entry functions *)
let constdecl f is_static e =
  let expected_k = if is_static then Tstatic(true) else Tdiscrete(false) in
  Misc.push_binding_level ();
  let ty = expression expected_k Env.empty e in
  Misc.pop_binding_level ();
  let tys = Types.gen (not (expansive e)) ty in
  tys

let fundecl loc f ({ f_kind = k; f_atomic = is_atomic;
                     f_args = pat_list; f_body = e } as body) =
  Misc.push_binding_level ();
  let expected_k = Interface.kindtype k in
  (* sets the kind of variables according to [k] *)
  (* vars in [pat_list] are values, i.e., *)
  (* they cannot be accessed with a last *)
  let h0 = env_of_pattern_list expected_k Env.empty pat_list in
  body.f_env <- h0;
  (* first type the body *)
  let ty_p_list = List.map (fun _ -> new_var ()) pat_list in
  pattern_list h0 pat_list ty_p_list;
  (* check that the pattern is total *)
  check_total_pattern_list pat_list;
  let ty_res = expression expected_k h0 e in
  Misc.pop_binding_level ();
  let ty_res = funtype loc expected_k pat_list ty_p_list ty_res in
  let tys = Types.gen true ty_res in
  tys

let implementation ff is_first impl =
  try
    match impl.desc with
    | Econstdecl(f, is_static, e) ->
       let tys = constdecl f is_static e in
       if is_first then Interface.add_type_of_value ff impl.loc f is_static tys
       else Interface.update_type_of_value ff impl.loc f is_static tys
    | Efundecl(f, body) ->
       let tys = fundecl impl.loc f body in
       if is_first then Interface.add_type_of_value ff impl.loc f true tys
       else Interface.update_type_of_value ff impl.loc f true tys
    | Eopen(modname) ->
       if is_first then Modules.open_module modname
    | Etypedecl(f, params, ty) ->
       if is_first then Interface.typedecl ff impl.loc f params ty
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
let implementation_list ff is_first impl_list =
  Misc.no_warning := not is_first;
  List.iter (implementation ff is_first) impl_list;
  Misc.no_warning := not is_first;
  impl_list
