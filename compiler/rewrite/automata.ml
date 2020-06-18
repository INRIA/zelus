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

(* removing automata statements *)
open Misc
open Location
open Ident
open Global
open Deftypes
open Zaux
open Zelus
open Initial

(* Translation of automata. *)
(* Strong transitions: *)
(* automaton
   | S1 -> locals in
           do eq_list
           unless | c'1 then do eq_list''1 in S''1(e'1) | ...
   | S2(p) -> ...p... | c2 then ...p...
   ...
   end

is translated into:

   local state, res in
   do  init state = S1
   and init res = false
   and
   match last state with
   | S1 -> reset
             present
             | c'1 -> eq_list''1
                      and state = S''1 and p1 = e'1 and res = true
             | ...
             else res = false
           every last res
   | S2 -> ... last p ...
   end
   and
   match state with
   | S1 -> reset
              locals in do eq_list
           every res
   | S2 -> ...p... *)

(* Weak transitions: *)
(* automaton
   | S1 -> locals in
           do eq_list
           until | c1 then do eq_list'1 in S'1(e1) | ... | ck then S'k(ek)
   | S2(p) -> ...p... | c2 then ...
   ...
   end

is translated into:

   local state, res in
   do init state = S1 in
   do init res = false in
   match last state with
   | S1 -> reset
              locals
            and
              present
              | c1 -> eq_list1 and
                      state = S'1 and next p1 = e1 and res = true
              | ...
              else res = false
           every last res
   | S2 -> ...last p...
   end

2. Builds a local table table_of_types for every new type
*)

let moduleident n =
  { n with source = (Modules.current_module ()) ^ "_" ^ n.source }

let eblock eq_list =
  { b_vars = []; b_locals = []; b_body = eq_list; b_loc = no_location;
    b_write = Deftypes.empty; b_env = Env.empty }
let eq_present l_true l_false =
  match l_true, l_false with
  | [], _ -> l_false
  | _, [] -> [eqmake (EQpresent(l_true, None))]
  | _ -> [eqmake (EQpresent(l_true, Some(eblock l_false)))]

let extend_block eq_list b_opt =
  match b_opt with
    | None -> eblock eq_list
    | Some(b) -> { b with b_body = eq_list @ b.b_body }


module TableOfTypes =
struct
  let table_of_types = ref []
  let add tyname ty_desc =
    table_of_types := (tyname, ty_desc) :: !table_of_types
  let make desc = { Zelus.desc = desc; Zelus.loc = no_location }
  let flush continuation =
    let translate (tyname, ty_desc) continuation =
      let n, params, ty_desc =
        Interface.type_decl_of_type_desc tyname ty_desc in
      make (Etypedecl(n, params, ty_desc)) :: continuation
    in
      let continuation =
        List.fold_right translate !table_of_types continuation in
      table_of_types := [];
      continuation
end

let constr c ty_list =
  Deftypes.make
    (Deftypes.Tconstr(Modules.qualify c, ty_list, Deftypes.no_abbrev()))

(* introduce a new type for an enumerated type. This should be a sum type *)
(* type ('a1,...,'ak) state_k = St1 [of 'a1] | ... | Stm [of 'an] *)
(* as it was in Lucid Synchrone. *)
(* Since the language only has 0-arity constructors, we take the following *)
(* type state_k = St1 | ... | Stm *)
(* we use state variables to store the parameters of a state *)
(* this is bad in term of execution time and memory as we allocate the *)
(* sum of variables used in parameters instead of the max *)
let intro_type s_h_list =

  (* we introduce a new type *)
  let name = "state__" ^ (string_of_int(symbol#name)) in

  (* introduce a new name for every parameterized state. *)
  (* for the moment, we do not share them *)
  (* [states] is a set of names [n1;...;nk] and *)
  (* [n_to_parameters] associate a list of parameters to a state name *)
  let states_and_variables_for_parameters s_h_list =
    let variable (states, n_to_parameters) { s_state = statepat } =
      match statepat.desc with
        | Estate0pat(n) -> (moduleident n) :: states, n_to_parameters
        | Estate1pat(n, n_list) ->
            (moduleident n) :: states, Env.add n n_list n_to_parameters in
    List.fold_left variable ([], Env.empty) s_h_list in

  (* build variants *)
  let variants states type_res =
    let variant n =
      { qualid = Modules.qualify (Ident.name n);
        info = { constr_arg = []; constr_res = type_res;
                 constr_arity = 0 } } in
    List.map variant states in

  (* build the result type *)
  let type_res = constr name [] in
  let states, n_to_parameters = states_and_variables_for_parameters s_h_list in
  let v_list = variants states type_res in
  let typ_desc = { type_desc = Variant_type(v_list); type_parameters = [] } in
  (* we add it to the global environment *)
  Modules.add_type name typ_desc;
  List.iter2
    (fun n { info = v } -> Modules.add_constr (Ident.name n) v) states v_list;
  (* and the environment of state types *)
  TableOfTypes.add name typ_desc;
  (* compute the set of variables needed for storing parameters *)
  type_res, n_to_parameters

let state_value ty =
  let mem = Deftypes.previous Deftypes.empty_mem in
  { Deftypes.t_sort = Deftypes.Smem (Deftypes.initialized mem);
    Deftypes.t_typ = ty }

let state_parameter is_init ty =
  let mem = Deftypes.previous Deftypes.empty_mem in
  { Deftypes.t_sort =
      Deftypes.Smem (if is_init then Deftypes.initialized mem else mem);
    Deftypes.t_typ = ty }

(** Adds variables used for state parameters to the environment *)
(** we consider that a parameter variable can be both modified/red with *)
(** [p = ...], [...p...], [...last p...] *)
let env_of_parameters n_to_parameters s_h_list se_opt =
  (* test whether or not a state equals [se_opt] *)
  let equalstate se_opt { desc = desc } =
    match se_opt, desc with
       Some({ desc = Estate1(s1, _)}), Estate1pat(s2, _) when s1 = s2 -> true
      | _ -> false in
  (* extends the global environment [env] with parameters of the *)
  (* different state handlers. Every parameter becomes a state variable *)
  let entry is_init n { Deftypes.t_typ = ty } acc =
    Env.add n (state_parameter is_init ty) acc in
  let add acc { s_state = statepat; s_env = env } =
    let is_init = equalstate se_opt statepat in
    Env.fold (entry is_init) env acc in
  (* define an environment *)
  let env = List.fold_left add Env.empty s_h_list in

  (* if an initial state [Sk(e1,...,en)] is given *)
  (* add equations [init p1 = e1 and ... and pn = en] *)
  let eq_list =
    match se_opt with
      | None | Some({ desc = Estate0 _ }) ->
          (* the initial state is the first one or has no parameter *)
          []
      | Some({ desc = Estate1(n, e_list) }) ->
          let n_list = Env.find n n_to_parameters in
          List.map2 (fun n e -> eq_init n e) n_list e_list in
  env, eq_list

(* Translate a generic block *)
let block locals body ({ b_locals = l_list; b_body = bo } as b) =
  let l_list = locals l_list in
  (* translate the body. *)
  let bo = body bo in
  { b with b_locals = l_list; b_body = bo }

(* translating a present statement *)
let present_handlers scondpat body p_h_list =
  List.map
    (fun ({ p_cond = scpat; p_body = b } as handler) ->
      { handler with p_cond = scondpat scpat; p_body = body b })
    p_h_list

(* translating an expression. [lnames] define state names [x] that must *)
(* be renamed into [last x] *)
let rec exp lnames ({ e_desc = desc } as e) =
  let desc = match desc with
    | Econst(i) -> Econst(i)
    | Econstr0(longname) -> Econstr0(longname)
    | Eglobal(longname) -> Eglobal(longname)
    | Eop(op, e_list) -> Eop(op, List.map (exp lnames) e_list)
    | Elocal(name) ->
       (* if [name] belong to [lnames], it is a state parameter *)
       (* that must be turn into [last name] *)
       if S.mem name lnames then Elast(name) else desc
    | Elast(name) -> Elast(name)
    | Etuple(e_list) -> Etuple(List.map (exp lnames) e_list)
    | Econstr1(c, e_list) -> Econstr1(c, List.map (exp lnames) e_list)
    | Eapp(app, e, e_list) ->
       Eapp(app, exp lnames e, List.map (exp lnames) e_list)
    | Erecord(label_e_list) ->
        Erecord(List.map
                  (fun (label, e) -> (label, exp lnames e)) label_e_list)
    | Erecord_access(e_record, longname) ->
       Erecord_access(exp lnames e_record, longname)
    | Erecord_with(e_record, label_e_list) ->
       Erecord_with(exp lnames e_record,
		    List.map
                      (fun (label, e) -> (label, exp lnames e)) label_e_list)
    | Etypeconstraint(e, ty) -> Etypeconstraint(exp lnames e, ty)
    | Eseq(e1, e2) -> Eseq(exp lnames e1, exp lnames e2)
    | Eperiod { p_phase = p1; p_period = p2 } ->
       Eperiod { p_phase = Misc.optional_map (exp lnames) p1;
                 p_period = exp lnames p2 }
    | Elet(l, e) -> Elet(local lnames l, exp lnames e)
    | Eblock(b, e) -> Eblock(block_eq_list lnames b, exp lnames e)
    | Epresent(p_h_list, e_opt) ->
        let e_opt = Misc.optional_map (exp lnames) e_opt in
        let p_h_list = present_handler_exp_list lnames p_h_list in
        Epresent(p_h_list, e_opt)
    | Ematch(total, e, m_h_list) ->
        let e = exp lnames e in
        let m_h_list = match_handler_exp_list lnames m_h_list in
        Ematch(total, e, m_h_list) in
    { e with e_desc = desc }

(** Translating an equation. [lnames] defines names [x] that must be *)
(* renamed into [last x] *)
and equation lnames ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(pat, e) -> { eq with eq_desc = EQeq(pat, exp lnames e) }
  | EQpluseq(n, e) -> { eq with eq_desc = EQpluseq(n, exp lnames e) }
  | EQinit(n, e0) ->
     { eq with eq_desc = EQinit(n, exp lnames e0) }
  | EQnext(n, e, e0_opt) ->
     { eq with eq_desc = EQnext(n, exp lnames e,
                                optional_map (exp lnames) e0_opt) }
  | EQder(n, e, e0_opt, p_h_e_list) ->
     { eq with eq_desc =
                 EQder(n, exp lnames e, optional_map (exp lnames) e0_opt,
                       present_handler_exp_list lnames p_h_e_list) }
  | EQemit(name, e_opt) ->
     { eq with eq_desc = EQemit(name, optional_map (exp lnames) e_opt) }
  | EQmatch(total, e, m_h_list) ->
     let m_h_list = match_handler_block_eq_list lnames m_h_list in
     { eq with eq_desc = EQmatch(total, exp lnames e, m_h_list) }
  | EQpresent(p_h_b_eq_list, b_opt) ->
     let p_h_b_eq_list =
       present_handler_block_eq_list lnames p_h_b_eq_list in
     let b_opt =
       match b_opt with
       | None -> None | Some(b) -> Some(block_eq_list lnames b) in
     { eq with eq_desc = EQpresent(p_h_b_eq_list, b_opt) }
  | EQautomaton(is_weak, state_handler_list, se_opt) ->
     automaton lnames is_weak state_handler_list se_opt
  | EQreset(res_eq_list, e) ->
     let res_eq_list = equation_list lnames res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, exp lnames e) }
  | EQand(and_eq_list) ->
     let and_eq_list = equation_list lnames and_eq_list in
     { eq with eq_desc = EQand(and_eq_list) }
  | EQbefore(before_eq_list) ->
     let before_eq_list = equation_list lnames before_eq_list in
     { eq with eq_desc = EQbefore(before_eq_list) }
  | EQblock(b_eq_list) ->
     { eq with eq_desc = EQblock(block_eq_list lnames b_eq_list) }
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(x, e) -> Einput(x, exp lnames e)
	 | Eoutput _ -> desc
	 | Eindex(x, e1, e2) -> Eindex(x, exp lnames e1, exp lnames e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, exp lnames e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block_eq_list lnames b_eq_list in
     { eq with eq_desc = EQforall { body with for_index = i_list;
					      for_init = init_list;
					      for_body = b_eq_list } }

and equation_list lnames eq_list = List.map (equation lnames) eq_list

and block_eq_list lnames b =
  let locals l_list = List.map (local lnames) l_list in
  let body eq_list = equation_list lnames eq_list in
  block locals body b

and present_handler_exp_list lnames p_h_e_list =
  present_handlers (scondpat lnames) (exp lnames) p_h_e_list

and present_handler_block_eq_list lnames p_h_b_eq_list =
  present_handlers (scondpat lnames) (block_eq_list lnames) p_h_b_eq_list

and match_handler_exp_list lnames m_h_list =
  List.map
    (fun ({ m_body = e } as handler) ->
      { handler with m_body = exp lnames e }) m_h_list

and match_handler_block_eq_list lnames m_h_list =
  List.map
    (fun ({ m_body = b } as handler) ->
      { handler with m_body = block_eq_list lnames b }) m_h_list

and local lnames ({ l_eq = eq_list } as l) =
  { l with l_eq = equation_list lnames eq_list }

and scondpat lnames ({ desc = desc } as scpat) =
    let desc = match desc with
      | Econdand(scpat1, scpat2) ->
         Econdand(scondpat lnames scpat1, scondpat lnames scpat2)
      | Econdor(scpat1, scpat2) ->
         Econdor(scondpat lnames scpat1, scondpat lnames scpat2)
      | Econdexp(e) -> Econdexp(exp lnames e)
      | Econdpat(e, p) -> Econdpat(exp lnames e, p)
      | Econdon(scpat, e) -> Econdon(scondpat lnames scpat, exp lnames e) in
    { scpat with desc = desc }

(** Translating an automaton *)
(** [eq_list] is a list of equations. The translation returns *)
(** an extended list containing [eq_list] and new equations *)
and automaton lnames is_weak handler_list se_opt =
  (* introduce a sum type to represent states and *)
  (* build an environment which associate parameters to states *)
  let statetype, n_to_parameters = intro_type handler_list in

  (* for a parameterized state, generate [n = e] when calling the state *)
  (* adds equations [init n_1 = e_1 and ... and init n_k = e_k] *)
  (* for the initial state if it is entered with an initial value *)
  let env, eq_list =
    env_of_parameters n_to_parameters handler_list se_opt  in

  let longident n = Modules.longname (Ident.name (moduleident n)) in

  (* the name of the initial state *)
  let initial =
    match se_opt with
      | None ->
          (* the initial state is the first in the list *)
          begin match (List.hd handler_list).s_state.desc with
          | Estate0pat(n) -> longident n | _ -> assert false
        end
      | Some({ desc = Estate0(n) } | { desc = Estate1(n, _) }) -> longident n in

  (* translate states *)
  let translate_statepat lnames statepat =
    let desc, lnames =
      match statepat.desc with
      | Estate0pat(n) -> Econstr0pat(longident n), lnames
      | Estate1pat(n, l) ->
         Econstr0pat(longident n),
         List.fold_left (fun acc m -> S.add m acc) lnames l in
    { p_desc = desc; p_loc = statepat.loc;
      p_typ = statetype; p_caus = Defcaus.no_typ; p_init = Definit.no_typ },
  lnames in

  (* translating a state *)
  let translate_state lnames { desc = desc; loc = loc } =
    (* make an equation [n = e] *)
    let eqmake n e =
      eqmake (EQeq(varpat n e.e_typ, exp lnames e)) in
    match desc with
      | Estate0(n) ->
          { e_desc = Econstr0(longident n);
            e_loc = loc;
            e_typ = statetype;
            e_caus = Defcaus.no_typ;
            e_init = Definit.no_typ }, []
      | Estate1(n, e_list) ->
          let n_list = Env.find n n_to_parameters in
          { e_desc = Econstr0(longident n);
            e_loc = loc;
            e_typ = statetype;
            e_caus = Defcaus.no_typ;
            e_init = Definit.no_typ },
          List.map2 eqmake n_list e_list in

  (* [state_name] is the target state computed in the current step *)
  (* [reset_name] is the target reset bit computed in the current step *)
  let state_name = Ident.fresh "s" in
  let reset_name = Ident.fresh "r" in

  let state_var n = var n statetype in
  let bool_var n = var n typ_bool in
  let state_last n = last n statetype in
  let bool_last n = last n typ_bool in

  (* Translation of an escape handler *)
  let escape lnames { e_cond = e; e_reset = r; e_block = b_opt;
	       e_next_state = se; e_env = h0; e_zero = zero } =
    let e = scondpat lnames e in
    let b_opt = Misc.optional_map (block_eq_list lnames) b_opt in
    let se, eq_list_se = translate_state lnames se in
    { p_cond = e; p_env = h0;
      p_body =
        extend_block
          ((eq_make state_name se) ::
             (eq_make reset_name (bool r)) :: eq_list_se) b_opt;
      p_zero = zero } in

  (* Translation of strong transitions *)
  let strong lnames { s_state = statepat; s_body = b; s_trans = trans } =
    let pat, snames = translate_statepat lnames statepat in
    (* translate the escape expression in which a state parameter [x] *)
    (* becomes [last x] *)
    let p_h_list = List.map (escape snames) trans in
    let handler_to_compute_current_state =
      eblock [eq_reset (eq_present p_h_list
			  [eq_make reset_name efalse])
                       (bool_last reset_name)] in
    let handler_for_current_active_state =
      let b = block_eq_list lnames b in
      eblock [eq_reset [eq_block b] (bool_var reset_name)] in
    (pat, handler_to_compute_current_state),
    (pat, handler_for_current_active_state) in

  (* This function computes what to do with a automaton with weak transitions *)
  (* a single match/with is generated *)
  let weak lnames { s_state = statepat; s_body = b; s_trans = trans } =
    let pat, lnames = translate_statepat lnames statepat in
    let p_h_list = List.map (escape lnames) trans in
    let b = block_eq_list lnames b in
    let eq_next_state =
      eq_present p_h_list [eq_make reset_name efalse] in
    let b = { b with b_body = eq_next_state @ b.b_body } in
    pat, eblock [eq_reset [eq_block b] (bool_last reset_name)] in

  (* the code generated for automata with strong transitions *)
  let strong_automaton lnames handler_list eq_list =
    let handlers = List.map (strong lnames) handler_list in
    let handler_to_compute_current_state_list,
        handler_for_current_active_state_list = List.split handlers in
    (eq_match (state_last state_name)
              (List.map
                 (fun (pat, body) ->
                   { m_pat = pat; m_body = body; m_env = Env.empty;
                     m_reset = false; m_zero = false })
                 handler_to_compute_current_state_list)) ::
       (eq_match (state_var state_name)
              (List.map (fun (pat, body) ->
                   { m_pat = pat; m_body = body; m_env = Env.empty;
                     m_reset = false; m_zero = false })
                        handler_for_current_active_state_list)) :: eq_list in
  (* the code for automatama with weak transitions *)
  let weak_automaton lnames handler_list eq_list =
    let handlers = List.map (weak lnames) handler_list in
    (eq_match (state_last state_name)
              (List.map
                 (fun (pat, body) ->
                   { m_pat = pat; m_body = body; m_env = Env.empty;
                     m_reset = false; m_zero = false }) handlers)) :: eq_list in
  (* the result *)
  let statetype_entry = state_value statetype in
  let typ_bool_entry = state_value typ_bool in
  let env =
    Env.add state_name statetype_entry
            (Env.add reset_name typ_bool_entry env) in
  (* translate the automaton *)
  let eq_list =
    if is_weak then weak_automaton lnames handler_list eq_list
    else strong_automaton lnames handler_list eq_list in
  (* initial state and reset value *)
  let eq_list =
    (eq_init state_name (emake (Econstr0(initial)) statetype)) ::
    (eq_init reset_name efalse) :: eq_list in
  Zaux.eq_block (Zaux.make_block env eq_list)

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> impl
    | Econstdecl(n, is_static, e) ->
        let e = exp S.empty e in
        { impl with desc = Econstdecl(n, is_static, e) }
    | Efundecl(n, ({ f_body = e } as body)) ->
        { impl with desc = Efundecl(n, { body with f_body = exp S.empty e }) }

let implementation_list impl_list =
  let impl_list = Misc.iter implementation impl_list in
  TableOfTypes.flush impl_list
