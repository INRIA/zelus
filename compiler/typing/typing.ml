(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
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
  | Types.Unify -> error loc (Ekind_clash(left_k, right_k))

let sort_less_than loc sort expected_k =
  match expected_k, sort with
  | Tstatic _, Sstatic -> ()
  | Tstatic _, _ -> error loc (Ekind_clash(Deftypes.Tany, expected_k))
  | _ -> ()

let check_is_vec loc actual_ty =
  try
    let ty_arg, _ = Types.filter_vec actual_ty in ty_arg
  with
    | Types.Unify -> error loc Esize_of_vec_is_undetermined
      
(* An expression is expansive if it is not an immediate value *)
let rec expansive { e_desc = desc } =
  match desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> false
    | Etuple(e_list) -> List.exists expansive e_list
    | Erecord(l_e_list) -> List.exists (fun (_, e) -> expansive e) l_e_list
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> expansive e
    | _ -> true

let check_statefull loc expected_k =
  if not (Types.is_statefull_kind expected_k)
  then error loc Ekind_not_combinatorial

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
    | Smem({ m_init = Some None } as m) ->
       tentry.t_sort <- Smem { m with m_init = None }
    | _ -> () in
  Env.iter mark first_h

(** Remove the sort "last" to the set [h] *)
let remove_last_to_env h =
  let remove ({ t_sort = sort } as t_entry) =
    let sort = match sort with
      | Sstatic | Sval | Svar _ -> sort | Smem _ -> Deftypes.value in
    { t_entry with t_sort = sort } in
  Env.map remove h

(** Variables in a pattern *)
let vars pat = Vars.fv_pat S.empty S.empty pat

(** Types for local identifiers *)
let var loc h n =
  try Env.find n h
  with Not_found -> error loc (Evar_undefined(n))
							 
let typ_of_var loc h n = let { t_typ = typ } = var loc h n in typ

let last loc h n =
  let { t_sort = sort; t_typ = typ } as entry = var loc h n in 
  (* [last n] is allowed only if [n] is a state variable *)
  begin match sort with
	| Sstatic | Sval | Svar _ -> error loc (Elast_undefined(n))
	| Smem (m) ->
	   entry.t_sort <- Smem { m with m_previous = true }
  end; typ

let der loc h n = typ_of_var loc h n

let pluseq loc h n =
  (* check that a name [n] is declared with a combination function *)
  let { t_typ = typ; t_sort = sort } = var loc h n in
    match sort with
    | Sval | Svar { v_combine = None } | Smem { m_combine = None } ->
					  error loc (Ecombination_function(n))
    | _ -> typ
	     
(** Types for global identifiers *)
let global loc lname =
  let { qualid = qualid; info = { value_typ = tys } } = find_value loc lname in
  qualid, Types.instance_of_type tys

let global_with_instance loc lname =
  let { qualid = qualid; info = { value_typ = tys } } = find_value loc lname in
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
  | Sstatic
  | Sval
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
  | Sstatic | Sval | Svar _ -> assert false
  | Smem m -> entry.t_sort <- Smem { m with m_init = Some(None) } in
  S.iter set dv

(* set the variables from [dv] to be derivatives *)
let set_derivative loc dv h =
  let set x =
    let { t_sort = sort } as entry = 
      try Env.find x h with Not_found -> assert false in
  match sort with
  | Sstatic | Sval | Svar _ -> assert false
  | Smem m -> entry.t_sort <- Smem { m with m_kind = Some(Cont) } in
  S.iter set dv

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
let constant loc expected_ty = function
  | Cimmediate(i) ->
     let actual_ty = immediate(i) in
     unify loc expected_ty actual_ty
  | Cglobal(lname) ->
     let qualid, actual_ty = global loc lname in 
     unify loc expected_ty actual_ty
	   
(* Typing the declaration of variables. The result is a typing environment *)
let vardec_list expected_k n_list =
  let default loc expected_ty c_opt = function
  | Init(v) ->
     (* the initialization must appear in a statefull function *)
     if not (Types.is_statefull_kind expected_k)
     then error loc Ekind_not_combinatorial;
     constant loc expected_ty v;
     Deftypes.Smem
       (Deftypes.cmem c_opt { empty_mem with m_init = Some(Some(v)) })
  | Default(v) ->
     constant loc expected_ty v;
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
	 | Tcont -> Deftypes.Smem (Deftypes.cmem c_opt Deftypes.empty_mem) in
    Env.add n { t_typ = expected_ty; t_sort = sort } h0 in
  List.fold_left vardec Env.empty n_list
 
(** Computes the set of names defined in a list of definitions *)
let rec build (names, inames) { eq_desc = desc } =
  (* block *)
  let block_with_bounded (names, inames) { b_vars = b_vars; b_body = eq_list } =
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
       S.union inames (if is_weak then S.diff esc_inames bounded else esc_inames)
     in
     List.fold_left handler (names, inames) sh_list
  | EQforall { for_index = in_list; for_init = init_list } ->
     let index (names, inames) { desc = desc } =
       match desc with
       | Einput _ | Eindex _ -> names, inames
       | Eoutput(_, n) -> S.add n names, inames in
     let init (names, inames) { desc = desc } =
       match desc with
       | Einit_last(n, _) | Einit_value(n, _, _) -> S.add n names, inames in
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
       | Deftypes.Tdiscrete true ->
	  if S.mem n inames then Deftypes.imemory
	  else Deftypes.Smem (Deftypes.empty_mem) in 
     Env.add n { t_typ = Types.new_var (); t_sort = sort } acc) names Env.empty
	 
let env_of_scondpat scpat =
  let rec env_of acc { desc = desc } =
    match desc with
    | Econdand(sc1, sc2) -> env_of (env_of acc sc1) sc2
    | Econdor(sc, _) | Econdon(sc, _) -> env_of acc sc
    | Econdexp _ -> acc
    | Econdpat(_, pat) -> Vars.fv_pat S.empty acc pat in
  let acc = env_of S.empty scpat in
  S.fold (fun n acc -> Env.add n { t_typ = Types.new_var (); t_sort = Sval } acc)
	 acc Env.empty

let env_of_statepat spat =
  let rec env_of acc { desc = desc } =
    match desc with
    | Estate0pat _ -> acc
    | Estate1pat(_, l) -> List.fold_left (fun acc n -> S.add n acc) acc l in
  let acc = env_of S.empty spat in
  S.fold (fun n acc -> Env.add n { t_typ = Types.new_var (); t_sort = Sval } acc)
	 acc Env.empty
	 
let env_of_pattern is_static h0 pat =
  let acc = Vars.fv_pat S.empty S.empty pat in
  let sort = if is_static then Sstatic else Sval in
  S.fold (fun n acc ->
	  Env.add n { t_typ = Types.new_var (); t_sort = sort } acc)
	 acc h0

(* the [n-1] first arguments are static. If [expected_k] is static *)
(* the last one two *)
let env_of_pattern_list expected_k env p_list =
  let p_list, p = Misc.firsts p_list in
  let env = List.fold_left (env_of_pattern true) env p_list in
  let is_static = match expected_k with | Tstatic(k) -> k | _ -> false in
  env_of_pattern is_static env p

let env_of_pattern pat = env_of_pattern false Env.empty pat
					
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
     let qualid, { constr_res = ty_res } = constr loc c0 in
     unify_pat pat ty ty_res;
     pat.p_desc <- Econstr0pat(Lident.Modname(qualid));
     (* type annotation *)
     pat.p_typ <- ty
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
    let h0 = env_of_pattern pat in
    pattern h0 pat pat_ty;
    mh.m_env <- h0;
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
  let handler ({ p_cond = scpat; p_body = b } as ph) =
    (* local variables from [scpat] cannot be accessed through a last *)
    let h0 = env_of_scondpat scpat in
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

let block locals body expected_k h 
    ({ b_vars = n_list; b_locals = l_list; b_body = bo } as b) expected_ty =
  (* initialize the local environment *)
  let h0 = vardec_list expected_k n_list in
  let h = Env.append h0 h in
  let new_h = locals expected_k h l_list in
  let defined_names = body expected_k new_h bo in
  (* check that every local variable from [l_list] appears in *)
  (* [defined_variable] and that initialized state variables are not *)
  (* re-initialized in the body *)
  let defined_names =
    check_definitions_for_every_name defined_names n_list in
  (* annotate the block with the set of written variables and environment *)
  b.b_write <- defined_names;
  b.b_env <- h0;
  new_h, defined_names

(* [expression expected_k h e] returns the type for [e] *)
let rec expression expected_k h ({ e_desc = desc; e_loc = loc } as e) =
  let ty = match desc with
    | Econst(i) -> immediate i  
    | Elocal(x) ->
       let { t_typ = typ; t_sort = sort } = var loc h x in
       sort_less_than loc sort expected_k;
       typ
    | Eglobal { lname = lname } -> 
       let qualid, typ_instance, ty = global_with_instance loc lname in 
       e.e_desc <- Eglobal { lname = Lident.Modname(qualid);
			     typ_instance = typ_instance }; ty
    | Elast(x) -> last loc h x
    | Etuple(e_list) ->
       product (List.map (expression expected_k h) e_list)
    | Eop(Eaccess, [e1; e2]) ->
      (* Special typing for [e1.(e2)]. [e1] must be of type [ty[size]]  *)
      (* with [size] a known expression at that point *)
      let ty = expression expected_k h e1 in
      let ty_res = check_is_vec e1.e_loc ty in
      expect expected_k h e2 Initial.typ_int; ty_res
    | Eop(op, e_list) ->
       operator expected_k h loc op e_list
    | Eapp({ app_statefull = is_statefull }, e, e_list) ->
       apply loc is_statefull expected_k h e e_list
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
  (* check that ty belongs to kind expected_k *)
  type_is_in_kind loc expected_k ty;
  (* type annotation *)
  e.e_typ <- ty;
  ty

(** Convert an expression into a size expression *)
and size_of_exp { e_desc = desc; e_loc = loc } =
  match desc with
  | Econst(Eint(i)) -> Tconst(i)
  | Elocal(n) -> Tname(n)
  | Eglobal { lname = Lident.Modname(qualid) } -> Tglobal(qualid)
  | Eapp(_, { e_desc = Eglobal { lname = Lident.Modname(qualid) } }, [e1; e2])
       when qualid = Initial.pervasives_name "+" ->
     Top(Tplus, size_of_exp e1, size_of_exp e2)
  | Eapp(_, { e_desc = Eglobal { lname = Lident.Modname(qualid) } }, [e1; e2])
       when qualid = Initial.pervasives_name "-" ->
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
       Tcont, [Initial.typ_unit], Initial.typ_zero
    | Eaccess -> assert false in
  less_than loc actual_k expected_k;
  List.iter2 (expect expected_k h) e_list ty_args;
  ty_res


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
       let expected_k = lift e.e_loc expected_k actual_k in
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
        let actual_ty = typ_of_var loc h n in
	expect (Types.lift_to_discrete expected_k) h e0 actual_ty;
        (* sets that every variable from [di] is initialized *)
	let di = S.singleton n in
	set_init loc di h;
	{ Deftypes.empty with di = di }
    | EQnext(n, e, e0_opt) ->
        (* a next is valid only in a discrete context *)
        less_than loc (Tdiscrete(true)) expected_k;
        let actual_ty = typ_of_var loc h n in
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
        let actual_ty = der loc h n in
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
    | EQand(eq_list)
    | EQbefore(eq_list) -> equation_list expected_k h eq_list
    | EQemit(n, e_opt) ->
        less_than loc expected_k (Tdiscrete(true));
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
       (* A non local variable [x] defined in the body of the loop must be *)
       (* either declared in the initialization part [initialize ...] *)
       (* or used to define an output array [x out t] *)
       (* check that [n] appear in either [dv], [di] or [der] *)
       let merge { dv = dv; di = di; der = der } init_h out_h =
	 (* [di] must be empty *)
	 if not (S.is_empty di)
	 then error loc (Ealready_in_forall(S.choose di));
	 (* all variables in [dv] and [der] must appear either *)
	 (* in [init_h] or [out_h] *)
	 let belong_to n =
	   if not ((Env.mem n init_h) || (Env.mem n out_h))
	   then error loc (Ealready_in_forall(n)) in
	 S.iter belong_to dv;
	 S.iter belong_to der in

       (* outputs are either shared or state variables *)
       let sort = if Types.is_statefull_kind expected_k
		  then Deftypes.Smem Deftypes.empty_mem
		  else Deftypes.variable in

       (* bounds for loops must be static *)
       (* computes the set of array names returned by the loop *)
       (* declarations are red from left to right. For [i in e0..e1], *)
       (* compute the size [(e1 - e0) + 1)] for the arrays *)
       let index (in_h, out_h, out_right, size_opt)
		 { desc = desc; loc = loc } =
	 let size_of loc size_opt =
	   match size_opt with
	   | None -> error loc Esize_of_vec_is_undetermined
	   | Some(actual_size) -> actual_size in
	 match desc with
	 | Einput(i, e) ->
	    let ty = Types.new_var () in
	    let si = size_of loc size_opt in
	    expect Tany h e (Types.vec ty si);
	    Env.add i { t_typ = ty; t_sort = Sval } in_h,
	    out_h, out_right, size_opt
	 | Eoutput(i, j) ->
	    let ty_i = Types.new_var () in
	    let ty_j = typ_of_var loc h j in
	    let si = size_of loc size_opt in
	    unify loc (Types.vec ty_i si) ty_j;
	    in_h, Env.add i { t_typ = ty_i; t_sort = sort } out_h,
	    S.add j out_right, size_opt
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
	    out_h, out_right, size_opt in

       (* returns the set of names returned by the loop *)
       let init init_h { desc = desc; loc = loc } =
	 match desc with
	 | Einit_last(i, e) ->
	    let ty = typ_of_var loc h i in
	    expect expected_k h e ty;
	    Env.add i { t_typ = ty; t_sort = Deftypes.memory } init_h
	 | Einit_value(i, e, c_opt) ->
	    let ty = typ_of_var loc h i in
	    expect expected_k h e ty;
	    Misc.optional_unit (combine loc) ty c_opt;
	    Env.add i
		    { t_typ = ty; t_sort = Deftypes.default None c_opt } init_h in

       let in_h, out_h, out_right, _ =
	 List.fold_left index (Env.empty, Env.empty, S.empty, None) i_list in
       body.for_in_env <- in_h;
       body.for_out_env <- out_h;
       
       let init_h = List.fold_left init Env.empty init_list in
       (* the environment [h] is extended with [in_h], [out_h] and [init_h] *)
       let h = Env.append in_h (Env.append out_h (Env.append init_h h)) in
       let _, ({ dv = dv } as defnames) = block_eq_list expected_k h b_eq_list in
       (* check that every name in defnames is initialized or an output *)
       merge defnames init_h out_h;
       (* remove names in [out_h] from [defnames] and add [out_right] *)
       let out_left =
	 Env.fold (fun n _ acc -> S.add n acc) out_h S.empty in
       { defnames with dv = S.union (S.diff dv out_left) out_right } in
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

and local expected_k h ({ l_eq = eq_list } as l) =
  (* decide whether [last x] is allowed or not on every [x] from [h0] *)
  let h0 = env_of_eq_list expected_k eq_list in
  l.l_env <- h0;
  let new_h = Env.append h0 h in
  ignore (equation_list expected_k new_h eq_list);
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
  let is_zero_type = Types.is_continuous_kind expected_k in
    
  (* typing the body of the automaton *)
  let typing_handler h 
	({ s_state = statepat; s_body = b; s_trans = trans } as s) =
    let escape source_state h expected_k 
        ({ e_cond = scpat; e_reset = r; e_block = b_opt; 
           e_next_state = state } as esc) =
      (* type one escape condition *)
      let h0 = env_of_scondpat scpat in
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
    let h0 = env_of_statepat statepat in
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
let constdecl f e =
  let ty = expression (Tstatic(true)) Env.empty e in
  let tys = Types.gen (not (expansive e)) ty in
  (f, true, tys)

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
  (f, is_atomic, tys)

let implementation ff is_first impl =
  try
    match impl.desc with
    | Econstdecl(f, e) ->
       let f, is_atomic, tys = constdecl f e in
       if is_first then Interface.add_type_of_value ff impl.loc f is_atomic tys
       else Interface.update_type_of_value ff impl.loc f is_atomic tys
    | Efundecl(f, body) ->
       let f, is_atomic, tys = fundecl impl.loc f body in
       if is_first then Interface.add_type_of_value ff impl.loc f is_atomic tys
       else Interface.update_type_of_value ff impl.loc f is_atomic tys
    | Eopen(modname) ->
       if is_first then Modules.open_module modname
    | Etypedecl(f, params, ty) ->
       if is_first then Interface.typedecl ff impl.loc f params ty
  with
  | Typerrors.Error(loc, err) -> Typerrors.message loc err
						   
(* the main entry function *)
let implementation_list ff is_first impl_list =
  List.iter (implementation ff is_first) impl_list; impl_list
