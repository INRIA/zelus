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
   | S2(p) -> ...p... | c2 then ...
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
             | c'1 -> eq_list''1 and state = S''1 and p1 = e'1 and res = true
             | ...
             else res = false
           every last res
   | S2 -> ...
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
   | S2 -> ...p...
   end

2. Builds a local table table_of_types for every new type
*)

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
  let flush continuation =
    let translate (tyname, ty_desc) continuation =
      let n, params, ty_desc =
        Interface.type_decl_of_type_desc tyname ty_desc in
      { Zelus.desc = Etypedecl(n, params, ty_desc); 
        Zelus.loc = no_location } :: continuation
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
(* as we consider a language with 0-arity constructor, we take the following *)
(* type state_k = St1 | ... | Stm *)
(* we use state variables to store the parameters of a state *)
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
        | Estate0pat(n) -> n :: states, n_to_parameters
        | Estate1pat(n, n_list) ->
            n :: states, Env.add n n_list n_to_parameters in
    List.fold_left variable ([], Env.empty) s_h_list in

  (* build variants *)
  let variants states type_res =
    let variant n =
      { qualid = Modules.qualify (Ident.name n);
        info = { constr_res = type_res } } in
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
let state_parameter is_init is_next ty = 
  let mem = if is_next then Deftypes.next Deftypes.empty_mem
	    else Deftypes.previous Deftypes.empty_mem in
  { Deftypes.t_sort =
      Deftypes.Smem
	(if is_init then Deftypes.initialized mem else mem);
    Deftypes.t_typ = ty }
    
(** returns [local x1,...,xn] from a typing env. [t1/x1,...,tn/xn] *)
let env_to_localvars env (x_list, t_env) =
  let add_local x t_entry (x_list, t_env) = 
    x :: x_list, Env.add x t_entry t_env in
  Env.fold add_local env (x_list, t_env)

let env_to_env acc env =
  let add x t_entry acc = Env.add x t_entry acc in
  Env.fold add env acc

(** Adds variables used for state parameters to the environment *)
(** we consider that a parameter variable can be both modified/red with *)
(** [next p = e], [p = ...], [...p...], [...last p...] *)
let env_of_parameters is_weak env eq_list n_to_parameters s_h_list se_opt =
  (* test whether or not a state equals [se_opt] *)
  let equalstate se_opt { desc = desc } =
    match se_opt, desc with
       Some({ desc = Estate1(s1, _)}), Estate1pat(s2, _) when s1 = s2 -> true
      | _ -> false in
  (* extends the global environment [env] with parameters of the *)
  (* different state handlers. Every parameter becomes a state variable *)
  let entry is_init n { Deftypes.t_typ = ty } acc =
    (* If the transition is weak, the argument is changed at the next step *)
    Env.add n (state_parameter is_init is_weak ty) acc in
  let add acc { s_state = statepat; s_env = env } = 
    let is_init = equalstate se_opt statepat in
    Env.fold (entry is_init) env acc in
  (* extends the global environment *)
  let env = List.fold_left add env s_h_list in

  (* if an initial state [Sk(e1,...,en)] is given *)
  (* add equations [init p1 = e1 and ... and pn = en] *)
  let eq_list =
    match se_opt with
      | None | Some({ desc = Estate0 _ }) -> 
          (* the initial state is the first one or has no parameter *)
          eq_list
      | Some({ desc = Estate1(n, e_list) }) ->
          let n_list = Env.find n n_to_parameters in
          List.fold_left2 
            (fun acc n e -> eq_init n e :: acc)
            eq_list n_list e_list in
  env, eq_list

(* Translate a generic block *)
let block locals body 
    ({ b_vars = n_list; b_locals = l_list; b_body = bo; b_env = b_env } as b) =
  let l_list = locals l_list in
  (* translate the body. This may introduce a fresh environment [env0] *)
  let env0, bo = body bo in
  (* these names are made local to the block *)
  let n_list, b_env = env_to_localvars env0 (n_list, b_env) in
  { b with b_locals = l_list; b_body = bo; b_vars = n_list; b_env = b_env }

(* translating a present statement *)
let present_handlers scondpat body p_h_list =
  List.map
    (fun ({ p_cond = scpat; p_body = b } as handler) ->
      { handler with p_cond = scondpat scpat; p_body = body b })
    p_h_list

let rec exp ({ e_desc = desc } as e) =
  let desc = match desc with
    | Econst(i) -> Econst(i)
    | Econstr0(longname) -> Econstr0(longname)
    | Eglobal(longname) -> Eglobal(longname)
    | Elocal(name) -> Elocal(name)
    | Elast(name) -> Elast(name)
    | Etuple(e_list) -> Etuple(List.map exp e_list)
    | Eapp(op, e_list) -> Eapp(op, List.map exp e_list)
    | Erecord(label_e_list) ->
        Erecord(List.map (fun (label, e) -> (label, exp e)) label_e_list)
    | Erecord_access(e, longname) -> Erecord_access(exp e, longname)
    | Etypeconstraint(e, ty) -> Etypeconstraint(exp e, ty)
    | Eseq(e1, e2) -> Eseq(exp e1, exp e2)
    | Eperiod(p) -> Eperiod(p)
    | Elet(l, e) -> Elet(local l, exp e)
    | Epresent(p_h_list, e_opt) ->
        let e_opt = Misc.optional_map exp e_opt in
        let p_h_list = present_handler_exp_list p_h_list in
        Epresent(p_h_list, e_opt)
    | Ematch(total, e, m_h_list) ->
        let e = exp e in
        let m_h_list = match_handler_exp_list m_h_list in
        Ematch(total, e, m_h_list) in
    { e with e_desc = desc }
            
(** Translating an equation. [env] defines the set of names already introduced *)
(** during the translation. [eq_list] is the list of equations already compiler *)
and equation (env, eq_list) ({ eq_desc = desc } as eq) =
  match desc with
    | EQeq(pat, e) -> env, { eq with eq_desc = EQeq(pat, exp e) } :: eq_list
    | EQpluseq(n, e) -> env, { eq with eq_desc = EQpluseq(n, exp e) } :: eq_list
    | EQinit(n, e0) -> 
      env, { eq with eq_desc = EQinit(n, exp e0) } :: eq_list
    | EQnext(n, e, e0_opt) -> 
      env, 
      { eq with eq_desc = EQnext(n, exp e, optional_map exp e0_opt) } :: eq_list
    | EQder(n, e, e0_opt, p_h_e_list) ->
        env, { eq with eq_desc =
            EQder(n, exp e, optional_map exp e0_opt, 
                  present_handler_exp_list p_h_e_list) } :: eq_list
    | EQemit(name, e_opt) -> 
        env, { eq with eq_desc = EQemit(name, optional_map exp e_opt) } :: eq_list
    | EQmatch(total, e, m_h_list) ->
        let m_h_list = match_handler_block_eq_list m_h_list in
        env, 
        { eq with eq_desc = EQmatch(total, exp e, m_h_list) } :: eq_list
    | EQpresent(p_h_b_eq_list, b_opt) ->
        let p_h_b_eq_list =
          present_handler_block_eq_list p_h_b_eq_list in
        let b_opt = 
          match b_opt with | None -> None | Some(b) -> Some(block_eq_list b) in
        env, { eq with eq_desc = EQpresent(p_h_b_eq_list, b_opt) } 
          :: eq_list
    | EQautomaton(is_weak, state_handler_list, se_opt) ->
        automaton is_weak env eq_list state_handler_list se_opt
    | EQreset(res_eq_list, e) ->
       let env, res_eq_list = equation_list env res_eq_list in
       env, { eq with eq_desc = EQreset(res_eq_list, exp e) } :: eq_list
    | EQblock(b_eq_list) ->
       env, { eq with eq_desc = EQblock(block_eq_list b_eq_list) } :: eq_list

and equation_list env eq_list = List.fold_left equation (env, []) eq_list

and block_eq_list b =
  let locals l_list = List.map local l_list in
  let body eq_list = equation_list Env.empty eq_list in
  block locals body b

and present_handler_exp_list p_h_e_list =
  present_handlers scondpat exp p_h_e_list

and present_handler_block_eq_list p_h_b_eq_list =
  present_handlers scondpat block_eq_list p_h_b_eq_list

and match_handler_exp_list m_h_list =
  List.map 
    (fun ({ m_body = e } as handler) -> 
      { handler with m_body = exp e }) m_h_list    

and match_handler_block_eq_list m_h_list =
  List.map 
    (fun ({ m_body = b } as handler) -> 
      { handler with m_body = block_eq_list b }) m_h_list    

and local ({ l_eq = eq_list; l_env = env } as l) =
  let env0, eq_list = equation_list Env.empty eq_list in
  if Env.is_empty env0 then { l with l_eq = eq_list }
  else
    let env = env_to_env env env0 in
    { l with l_eq = eq_list; l_env = env }
       
and scondpat ({ desc = desc } as scpat) =
    let desc = match desc with
      | Econdand(scpat1, scpat2) -> Econdand(scondpat scpat1, scondpat scpat2)
      | Econdor(scpat1, scpat2) -> Econdor(scondpat scpat1, scondpat scpat2)
      | Econdexp(e) -> Econdexp(exp e)
      | Econdpat(e, p) -> Econdpat(exp e, p)
      | Econdon(scpat, e) -> Econdon(scondpat scpat, exp e) in
    { scpat with desc = desc }
      
(** Translating an automaton *)
(** [eq_list] is a list of equations. The translation returns *)
(** an extended list containing [eq_list] and new equations *)
and automaton is_weak env eq_list handler_list se_opt =
  (* introduce a sum type to represent states and *)
  (* build an environment which associate parameters to states *)
  let statetype, n_to_parameters = intro_type handler_list in

  (* for a parameterized state, generate [n = e] when calling the state *)
  (* adds equations [init n_1 = e_1 and ... and init n_k = e_k] *)
  (* for the initial state if it is entered with an initial value *)
  let env, eq_list = 
    env_of_parameters
      is_weak env eq_list n_to_parameters handler_list se_opt  in

  let longident n = Modules.longname (Ident.name n) in

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
  let translate_statepat statepat =
    let desc = match statepat.desc with
        | Estate0pat(n) | Estate1pat(n, _) -> Econstr0pat(longident n) in
    { p_desc = desc; p_loc = statepat.loc;
      p_typ = statetype; p_caus = [] } in

  (* In case of a weak transition, the parameter [n] of the target *)
  (* state is changed with [next n = ...] *)
  let translate_state is_weak { desc = desc; loc = loc } =
    (* make an equation [n = e] or [next n = e] *)
    let eqmake n e =
      if is_weak then eqmake (EQnext(n, e, None))
      else eqmake (EQeq(varpat n e.e_typ, e)) in
    match desc with
      | Estate0(n) -> 
          { e_desc = Econstr0(longident n);
            e_loc = loc;
            e_typ = statetype; e_caus = [] }, []
      | Estate1(n, e_list) ->
          let n_list = Env.find n n_to_parameters in
          { e_desc = Econstr0(longident n);
            e_loc = loc;
            e_typ = statetype; e_caus = [] }, 
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
  let escape is_weak { e_cond = e; e_reset = r; e_block = b_opt; 
		       e_next_state = se; e_env = h0; e_zero = zero } =
    let se, eq_list_se = translate_state is_weak se in
    { p_cond = scondpat e; p_env = h0;
      p_body =
        extend_block
          ((eq_make state_name se) ::
             (eq_make reset_name (bool r))
           :: eq_list_se) b_opt;
      p_zero = zero } in
  
  (* This function computes what to do with a automaton with strong transitions *)
  let strong { s_state = statepat; s_body = b; s_trans = trans } =
    let pat = translate_statepat statepat in
    let p_h_list = List.map (escape false) trans in
    let handler_to_compute_current_state =
      eblock [eq_reset (eq_present p_h_list
			  [eq_make reset_name efalse])
                       (bool_last reset_name)] in
    let handler_for_current_active_state = 
      let b = block_eq_list b in
      eblock [eq_reset [eq_block b] (bool_var reset_name)] in
    (pat, handler_to_compute_current_state),
    (pat, handler_for_current_active_state) in

  (* This function computes what to do with a automaton with weak transitions *)
  (* a single match/with is generated *)
  let weak { s_state = statepat; s_body = b; s_trans = trans } =
    let pat = translate_statepat statepat in
    let p_h_list = List.map (escape true) trans in
    let b = block_eq_list b in
    let eq_next_state =
      eq_present p_h_list [eq_make reset_name efalse] in
    let b = { b with b_body = eq_next_state @ b.b_body } in
    pat, eblock [eq_reset [eq_block b] (bool_last reset_name)] in
  
  (* the code generated for automata with strong transitions *)
  let strong_automaton handler_list eq_list =
    let handlers = List.map strong handler_list in
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
  let weak_automaton handler_list eq_list =
    let handlers = List.map weak handler_list in
    (eq_match (state_last state_name)
             (List.map
                (fun (pat, body) ->
                 { m_pat = pat; m_body = body; m_env = Env.empty; 
                   m_reset = false; m_zero = false }) handlers)) :: eq_list in
  (* the result *)
  let statetype_entry = state_value statetype in
  let typ_bool_entry = state_value typ_bool in
  Env.add state_name statetype_entry (Env.add reset_name typ_bool_entry env),
  (* initial state and reset value *)
  let eq_list = 
    (eq_init state_name (emake (Econstr0(initial)) statetype)) :: 
      (eq_init reset_name efalse) :: eq_list in
  if is_weak then weak_automaton handler_list eq_list
  else strong_automaton handler_list eq_list

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> impl
    | Econstdecl(n, e) ->
        let e = exp e in
        { impl with desc = Econstdecl(n, e) }
    | Efundecl(n, ({ f_body = e } as body)) ->
        { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list =
  let impl_list = Misc.iter implementation impl_list in
  TableOfTypes.flush impl_list

