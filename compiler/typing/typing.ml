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

(* sets used to check that record definitions are exaustive *)
module SLident = Set.Make (Lident)

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

(* check that a safe function is only called in a discrete context *)
let safe loc is_safe expected_k =
  if not is_safe then
    match expected_k with
      | Deftypes.Tdiscrete _ -> ()
      | _ -> (* we treat [is_safe=true] as kind [Tdiscrete(false)] *)
	     error loc (Ekind_clash(Deftypes.Tdiscrete(false), expected_k))

(* An expression is expansive if it is not an immediate value *)
let rec expansive { e_desc = desc } =
  match desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> false
    | Etuple(e_list) -> List.exists expansive e_list
    | Erecord(l_e_list) -> List.exists (fun (_, e) -> expansive e) l_e_list
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> expansive e
    | _ -> true

let check_statefull loc expected_k =
  if not (Types.is_statefull expected_k) then error loc Ekind_not_combinatorial

let instance_of_type loc lname tys =
  try
    Types.instance_of_type tys
  with
    | Types.Unify -> error loc (Eglobal_is_a_function(lname))

let instance_of_type_signature loc lname tys =
  try
    Types.instance_of_type_signature tys
  with
    | Types.Unify -> error loc (Eapplication_of_non_function(lname))

(** The type of states in automata *)
(** We constraint the use of automata such that a state can be entered *)
(** by reset of by history but with the constraint that *)
(** all transitions on that state must agree on one kind of transition. *)
(** Note that this is a restriction w.r.t Lucid Synchrone *)
type state = { mutable s_reset: bool option; s_parameters: typ list }

let check_target_state loc expected_reset actual_reset =
  match expected_reset with
    | None -> Some(actual_reset)
    | Some(expected_reset) -> 
        if expected_reset = actual_reset then Some(expected_reset)
	else error loc (Ereset_target_state(actual_reset, expected_reset))

(* Every shared variable defined in the initial state of an automaton *)
(* left weakly is considered to be an initialized state variable. *)
let turn_vars_into_memories h { dv = dv } =
  let add n acc = 
    let ({ t_sort = sort; t_typ = typ } as tentry) = Env.find n h in
    match sort with
    | Smem({ m_init = None } as m) ->
       Env.add n { tentry with t_sort = Smem { m with m_init = Some None } } acc
    | Sval | Svar _ | Smem _ -> acc  in
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
    | Smem({ m_init = Some None } as m) ->
       tentry.t_sort <- Smem { m with m_init = None }
    | _ -> () in
  Env.iter mark first_h

(** Remove the sort "last" to the set [h] *)
let remove_last_to_env h =
  let remove t_entry = { t_entry with t_sort = Deftypes.value } in
  Env.map remove h

(** Variables in a pattern *)
let vars pat = Vars.fv_pat S.empty S.empty pat

(** Types for local identifiers *)
let var h n =
  let { t_typ = typ } = Env.find n h in typ

let last loc h n =
  let { t_sort = sort; t_typ = typ } as entry = Env.find n h in 
  (* [last n] is allowed only if [n] is a state variable *)
  begin match sort with
	| Sval | Svar _ -> error loc (Elast_undefined(n))
	| Smem (m) ->
	   entry.t_sort <- Smem { m with m_previous = true }
  end; typ

let der h n =
  let { t_typ = typ } = Env.find n h in typ

let pluseq loc h n =
  (* check that a name [n] is declared with a combination function *)
  let { t_typ = typ; t_sort = sort } = Env.find n h in
  match sort with
    | Sval | Svar { v_combine = None } | Smem { m_combine = None } ->
      error loc (Ecombination_function(n))
    | _ -> typ
       
(** Types for global identifiers *)
let global loc lname =
  let { qualid = qualid; info = { value_typ = tys } } = find_value loc lname in
  qualid, instance_of_type loc lname tys

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
    (fun { dv = dv; di = di; der = der }
      { vardec_name = n; vardec_default = d_opt; vardec_loc = loc } ->
     let in_dv = S.mem n dv in
     let in_di = S.mem n di in
     let in_der = S.mem n der in
     (* check that n is defined by an equation *)
     if not (in_dv || in_di || in_der)  then error loc (Eequation_is_missing(n));
     (* check that it is not already initialized *)
     match d_opt with
       | Some(Init _) when in_di -> error loc (Ealready(Initial, n))
       | _ ->
	  (* otherwise, remove local names *)
	  { dv = if in_dv then S.remove n dv else dv;
	    di = if in_di then S.remove n di else di;
	    der = if in_der then S.remove n der else der })
    defined_names n_list
    
(* sets that a variable is defined by an equation [x = ...] or [next x = ...] *)
(* when [is_next = true] then [x] must be defined by equation [next x = ...] *)
(* [x = ...] otherwise *)
let set is_next loc dv h =
  let set x =
    let { t_sort = sort } as entry = 
      try Env.find x h with Not_found -> assert false in
  match sort with
  | Sval -> error loc (Ecannot_be_set(is_next, x))
  | Svar _ -> if is_next then error loc (Ecannot_be_set(is_next, x))
  | Smem ({ m_next = n_opt } as m) ->
     match n_opt with
     | None ->
	entry.t_sort <- Smem { m with m_next = Some(is_next) }
     | Some(n) -> if n <> is_next then error loc (Ecannot_be_set(is_next, x)) in
  S.iter set dv

(* set the variables from [dv] to be initialized *)
let set_init loc dv h =
  let set x =
    let { t_sort = sort } as entry = 
      try Env.find x h with Not_found -> assert false in
  match sort with
    | Sval | Svar _ -> assert false
    | Smem m -> entry.t_sort <- Smem { m with m_init = Some(None) } in
  S.iter set dv

(* set the variables from [dv] to be derivatives *)
let set_derivative loc dv h =
  let set x =
    let { t_sort = sort } as entry = 
      try Env.find x h with Not_found -> assert false in
  match sort with
    | Sval | Svar _ -> assert false
    | Smem m -> entry.t_sort <- Smem { m with m_kind = Some(Cont) } in
  S.iter set dv

(** Build the initial environment. *)
(* [set_env_with_value h0] sets the sort of names in [h0] to be value *)
let set_env_with_values h0 =
  let initialize _ entry = 
    entry.t_sort <- Sval;
    entry.t_typ <- Types.new_var () in
  Env.iter initialize h0

(* [set_env is_statefull h0] sets the sort to be a memory *)
(* when [is_statefull = true] *)
let set_env is_statefull h0 =
  let initialize _ ({ t_sort = sort } as entry) =
    entry.t_typ <- Types.new_var ();
    entry.t_sort <-
      match sort with
      | Svar _ when is_statefull -> Deftypes.Smem (Deftypes.empty_mem)
      | _ -> sort in
  Env.iter initialize h0


  (** Typing a declaration *)
(* Set the sort of variables in the environment. State variables *)
(** are only allowed when [is_statefull = true] *)
(** change the sort of names in [h0] according to what is declared *)
let vardec_list is_statefull n_list h0 =
  (* type checking of the combination function *)
  let combine loc expected_ty lname  =
    let { qualid = qualid; info = { value_typ = tys } } = 
      find_value loc lname in
    let actual_k, is_safe, ty_arg_list, ty_res = 
      instance_of_type_signature loc lname tys in
    (* the combination function must be safe *)
    safe loc is_safe Tany;
    (* and stateless *)
    less_than loc actual_k Tany;  
    (* Its signature must be [expected_ty * expected_ty -> expected_ty] *)
    match ty_arg_list with
    | [ty1; ty2] -> unify loc expected_ty ty1; unify loc expected_ty ty2
    | _ -> error loc (Earity_clash(2, List.length ty_arg_list)) in
  (* type checking of the declared default/init value *)
  let constant loc expected_ty = function
    | Cimmediate(i) ->
       let actual_ty = immediate(i) in
       unify loc expected_ty actual_ty
    | Cglobal(lname) ->
       let qualid, actual_ty = global loc lname in 
       unify loc expected_ty actual_ty in
  let default loc expected_ty c_opt  = function
    | Init(v) ->
       (* the initialization must appear in a statefull function *)
       if not is_statefull then error loc Ekind_not_combinatorial;
       constant loc expected_ty v;
       Deftypes.Smem
	 (Deftypes.cmem c_opt { empty_mem with m_init = Some(Some(v)) })
    | Default(v) ->
       constant loc expected_ty v;
       Deftypes.default (Some(v)) c_opt in
		 
  (* typing every declaration *)
  let vardec { vardec_name = n; vardec_default = d_opt; vardec_combine = c_opt;
	       vardec_loc = loc } =
    let expected_ty = Types.new_var () in
    let { t_sort = sort } as entry = Env.find n h0 in
    Misc.optional_unit (combine loc) expected_ty c_opt;
    let sort =
      match d_opt with
      | None ->
	 if is_statefull
	 then Deftypes.Smem (Deftypes.cmem c_opt Deftypes.empty_mem)
	 else Deftypes.default None c_opt
      | Some(d) -> default loc expected_ty c_opt d in
    entry.t_typ <- expected_ty;
    entry.t_sort <- sort in
  List.iter vardec n_list
 
(** The type of primitives and imported functions *)
let operator loc expected_k op =
  match op with
    | Eifthenelse ->
        let s = new_var () in
        op, Tany, true, [Initial.typ_bool; s; s], s
    | Eunarypre ->
        let s = new_var () in
        op, Tdiscrete(true), true, [s], s
    | Eminusgreater ->
        let s = new_var () in
        op, Tdiscrete(true), true, [s; s], s
    | Efby ->
        let s = new_var () in
        op, Tdiscrete(true), true, [s; s], s
    | Eup ->
        op, Tcont, true, [Initial.typ_float], Initial.typ_zero
    | Ehorizon ->
        op, Tcont, true, [Initial.typ_float], Initial.typ_zero
    | Eafter _ ->
        let s = new_var () in
        op, Tany, true, [s], s
    | Etest ->
        let s = new_var () in
        op, Tany, true, [Initial.typ_signal s], Initial.typ_bool
    (* | Edisc ->
        op, Tcont, true, [Initial.typ_float], Initial.typ_zero *)
    | Edisc ->
        let s = new_var () in
        op, Tcont, true, [s], Initial.typ_zero
    | Einitial ->
        op, Tcont, true, [], Initial.typ_zero
    | Eop(is_inline, lname) ->
        let { qualid = qualid; info = { value_typ = tys } } = 
	  find_value loc lname in
        let k, is_safe, ty_arg_list, ty_res = 
	  instance_of_type_signature loc lname tys in
        Eop(is_inline, Lident.Modname(qualid)), k, is_safe, ty_arg_list, ty_res
   | Eevery(is_inline, lname) ->
        (* a regular application with reset. The first argument is the reset *)
        (* condition *)
        let { qualid = qualid; info = { value_typ = tys } } = 
	  find_value loc lname in
        let k, is_safe, ty_arg_list, ty_res = 
	  instance_of_type_signature loc lname tys in
        Eop(is_inline, Lident.Modname(qualid)), k, is_safe, 
	(Types.zero_type expected_k) :: ty_arg_list, ty_res
 
(** Typing patterns *)
(* the kind of variables in [p] must be equal to [expected_k] *)
let rec pattern h pat ty =
  match pat.p_desc with
    | Ewildpat -> 
        (* type annotation *)
        pat.p_typ <- ty
    | Econstpat(im) ->
        unify_pat pat ty (immediate im);
        (* type annotation *)
        pat.p_typ <- ty
    | Econstr0pat(c0) ->
        let qualid, { constr_res = ty_res } = constr pat.p_loc c0 in
        unify_pat pat ty ty_res;
        pat.p_desc <- Econstr0pat(Lident.Modname(qualid));
        (* type annotation *)
        pat.p_typ <- ty
    | Evarpat(x) -> 
        unify_pat pat ty (var h x);
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
        unify_pat pat ty (var h x);
        (* type annotation *)
        pat.p_typ <- ty;
        pattern h p ty
    | Eorpat(p1, p2) -> 
        (* type annotation *)
        pat.p_typ <- ty;
        pattern h p1 ty;
        pattern h p2 ty
    
let pattern_list h pat_list ty_list = List.iter2 (pattern h) pat_list ty_list

(* check that a pattern is total *)
let check_total_pattern p =
  let is_exhaustive = Patternsig.check_activate p.p_loc p in
  if not is_exhaustive then error p.p_loc Epattern_not_total

let check_total_pattern_list p_list = List.iter check_total_pattern p_list
        
(** Typing a pattern matching. Returns defined names *)
let match_handlers body loc expected_k h total m_handlers pat_ty ty =
  let handler { m_pat = pat; m_body = b; m_env = h0 } =
    set_env_with_values h0;
    pattern h0 pat pat_ty;
    let h = Env.append h0 h in
    body expected_k h b ty in
  let defined_names_list = List.map handler m_handlers in
  (* check partiality/redundancy of the pattern matching *)
  let is_exhaustive = Patternsig.check_match_handlers loc m_handlers in
        
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
  let handler ({ p_cond = scpat; p_body = b; p_env = h0 } as ph) =
    (* local variables from [scpat] cannot be accessed through a last *)
    set_env_with_values h0;
    let h = Env.append h0 h in
    let is_zero = Types.is_continuous expected_k in
    scondpat expected_k is_zero h scpat;
    (* sets [zero = true] is [expected_k = Tcont] *)
    ph.p_zero <- is_zero;
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

let block locals body expected_k h 
    ({ b_vars = n_list; b_locals = l_list; 
       b_body = bo; b_env = h0 } as b) expected_ty =
  (* initialize the local environment *)
  vardec_list (Types.is_statefull expected_k) n_list h0;
  let h = Env.append h0 h in
  let new_h = locals expected_k h l_list in
  let defined_names = body expected_k new_h bo in
  (* check that every local variable from [l_list] appears in *)
  (* [defined_variable] and that initialized state variables are not *)
  (* re-initialized in the body *)
  let defined_names =
    check_definitions_for_every_name defined_names n_list in
  (* annotate the block with the set of written variables *)
  b.b_write <- defined_names;
  new_h, defined_names

(* [expression expected_k h e] returns the type for [e] *)
let rec expression expected_k h ({ e_desc = desc; e_loc = loc } as e) =
  let ty = match desc with
    | Econst(i) -> immediate i  
    | Elocal(x) -> var h x
    | Eglobal(lname) -> 
        let qualid, ty = global loc lname in 
        e.e_desc <- Eglobal(Lident.Modname(qualid)); ty
    | Elast(x) -> last loc h x
    | Etuple(e_list) ->
        product (List.map (expression expected_k h) e_list)
    | Eapp(op, e_list) ->
        let op, ty = app loc expected_k h op e_list in
        e.e_desc <- Eapp(op, e_list);
	ty
    | Econstr0(c0) ->
        let qualid, { constr_res = ty_res } = constr loc c0 in
        e.e_desc <- Econstr0(Lident.Modname(qualid)); ty_res
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
        period loc p;
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
    (* type annotation *)
    e.e_typ <- ty;
    ty
  
and period loc { p_phase = p1_opt; p_period = p2 } =
  (* check that all immediate values are strictly positive *)
  let check v = if v <= 0.0 then error loc (Eperiod_not_positive(v)) in
  check p2

(** Typing an expression with expected type [expected_type] *)
and expect expected_k h e expected_ty =
  let actual_ty = expression expected_k h e in
  unify_expr e expected_ty actual_ty

(** Typing an optional expression with expected type [expected_type] *)
(** [v] is the set of defined when the expression is present *)
and optional_expect expected_k h e_opt expected_ty v =
  match e_opt with
    | None -> S.empty
    | Some(e) -> 
        expect expected_k h e expected_ty; v

and app loc expected_k h op arg_list =
  let op, actual_k, is_safe, ty_arg_list, ty_res = operator loc expected_k op in
  (* check that the actual kind is less than the one from the calling context *)
  less_than loc actual_k expected_k;
  (* the call to un unsafe function is forbidden when not aligned *)
  (* a zero-crossing *)
  safe loc is_safe expected_k;
  try
    List.iter2 
      (fun e expected_ty -> expect expected_k h e expected_ty)
      arg_list ty_arg_list;
    op, ty_res
  with
    | Invalid_argument _ ->
        error loc (Earity_clash(List.length arg_list, List.length ty_arg_list))

(** Typing an equation. Returns the set of defined names *)
and equation expected_k h ({ eq_desc = desc; eq_loc = loc } as eq) =
  let defnames = match desc with
    | EQeq(p, e) ->
        let ty_e = expression expected_k h e in
        pattern h p ty_e; 
        (* check that the pattern is total *)
        check_total_pattern p;
	let dv = vars p in
	(* sets that every variable from [dv] has a current value *)
	set false loc dv h;
	{ Deftypes.empty with dv = dv }
    | EQpluseq(n, e) ->
        let actual_ty = expression expected_k h e in
        let expected_ty = pluseq loc h n in 
        unify loc expected_ty actual_ty;
	(* sets that every variable from [dv] has a current value *)
	let dv = S.singleton n in
	set false loc dv h;
	{ Deftypes.empty with dv = dv }
    | EQinit(n, e0) ->
        (* an initialization is valid only in a continuous or discrete context *)
        check_statefull loc expected_k;
        let actual_ty = var h n in
	expect (Types.lift_to_discrete expected_k) h e0 actual_ty;
        (* sets that every variable from [di] is initialized *)
	let di = S.singleton n in
	set_init loc di h;
	{ Deftypes.empty with di = di }
    | EQnext(n, e, e0_opt) ->
        (* a next is valid only in a discrete context *)
        less_than loc (Tdiscrete(true)) expected_k;
        let actual_ty = var h n in
	expect expected_k h e actual_ty;
	(* sets that every variable from [dv] has a next value *)
	let dv = S.singleton n in
	set true loc dv h;
	let di = 
	  match e0_opt with 
	    | None -> S.empty | Some(e) -> expect expected_k h e actual_ty; dv in
	(* sets that every variable from [di] is initialized *)
	set_init loc di h;
	{ Deftypes.empty with dv = dv; di = di }
    | EQder(n, e, e0_opt, p_h_e_list) ->
        (* integration is only valid in a continuous context *)
        less_than loc Tcont expected_k;
        let actual_ty = der h n in
        unify loc Initial.typ_float actual_ty;
	expect expected_k h e actual_ty;
        (* written names *)
	let der = S.singleton n in
	let di = 
	  optional_expect (Types.lift_to_discrete expected_k) h e0_opt 
	    Initial.typ_float der in
	(* sets that every variable from [di] is initialized *)
	set_init loc di h;
	(* sets that [n] is a derivative *)
	set_derivative loc der h;
	let _ = 
	  present_handler_exp_list 
	    loc expected_k h p_h_e_list None Initial.typ_float in
	let dv = if p_h_e_list = [] then S.empty else der in
	(* sets that every variable from [dv] has a current value *)
	set false loc dv h;
	{ dv = dv; di = di; der = der }
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
    | EQemit(n, e_opt) ->
        less_than loc expected_k (Tdiscrete(true));
        let ty_e = new_var () in
        let ty_name = var h n in
        begin match e_opt with 
            | None -> unify loc (Initial.typ_signal Initial.typ_unit) ty_name
            | Some(e) -> 
                unify loc (Initial.typ_signal ty_e) ty_name;
                expect expected_k h e ty_e 
        end;
        { Deftypes.empty with dv = S.singleton n }
    | EQblock(b_eq_list) ->
      snd (block_eq_list expected_k h b_eq_list) in
  (* set the names defined in the current equation *)
  eq.eq_write <- defnames;
  (* every equation must define at least a name *)
  if S.is_empty (Deftypes.names S.empty defnames)
  then warning loc Wequation_does_not_define_a_name;
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
  
(** Type a block when the body is a list of equations *)
and block_eq_list expected_k h b = 
  let locals expected_k h l_list =
    List.fold_left (local expected_k) h l_list in 
  block locals equation_list expected_k h b Initial.typ_unit

and local expected_k h { l_eq = eq_list; l_env = h0; l_loc = loc } =
  (* decide whether [last x] is allowed or not on every [x] from [h0] *)
  set_env (Types.is_statefull expected_k) h0;
  let h = Env.append h0 h in
  ignore (equation_list expected_k h eq_list);
  (* outside of the block, last values cannot be accessed anymore *)
  let h0 = remove_last_to_env h0 in
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
(* [is_reset = true] if [state] is entered by reset *)
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
  let is_zero_type = Types.is_continuous expected_k in
    
  (* typing the body of the automaton *)
  let typing_handler h 
	{ s_state = statepat; s_body = b; s_trans = trans; s_env = h0 } =
    let escape source_state h expected_k 
        ({ e_cond = scpat; e_reset = r; e_block = b_opt; 
           e_next_state = state; e_env = h0 } as esc) =
      (* type one escape condition *)
      set_env_with_values h0;
      let h = Env.append h0 h in
      scondpat expected_k is_zero_type h scpat;
      (* sets flag [zero = true] when [is_zero_type = true] *)
      esc.e_zero <- is_zero_type;
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
    set_env_with_values h0;
    begin match statepat.desc with
      | Estate0pat _ -> ()
      | Estate1pat(s, n_list) ->
          let { s_parameters = ty_list } = Env.find s def_states in
          List.iter2
	    (fun n ty -> unify statepat.loc (var h0 n) ty) n_list ty_list;
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

  (* finally, indicate for every state handler if it is entered by reset or not *)
  mark_reset_state def_states state_handlers;
  defined_names

let implementation ff impl =
  try
    match impl.desc with
      | Econstdecl(f, e) ->
          let ty = expression (Tdiscrete(false)) Env.empty e in
          let tys = Types.gen (not (expansive e)) (Tvalue(ty)) in
          Interface.addvalue ff impl.loc f true tys
      | Efundecl(f,{ f_kind = k; f_atomic = is_atomic;
		     f_args = pat_list; f_body = e; f_env = h0 }) ->
	  Misc.push_binding_level ();
	  let expected_k = Interface.kindtype k in
          (* var. in the pattern list [pat_list] cannot be accessed with a last *)
	  set_env_with_values h0;
          (* first type the body *)
          let ty_list = List.map (fun _ -> new_var ()) pat_list in
          pattern_list h0 pat_list ty_list;
          (* check that the pattern is total *)
          check_total_pattern_list pat_list;
          let ty = expression expected_k h0 e in
          Misc.pop_binding_level ();
	  let tys = Types.gen true (Tsignature(expected_k, true, ty_list, ty)) in
          (* then add the corresponding entries in the global environment *)
          Interface.addvalue ff impl.loc f is_atomic tys
    | Eopen(modname) ->
        Modules.open_module modname
    | Etypedecl(f, params, ty) ->
        Interface.typedecl ff impl.loc f params ty
  with
    | Typerrors.Error(loc, err) -> Typerrors.message loc err

let implementation_list ff impl_list =
  List.iter (implementation ff) impl_list
