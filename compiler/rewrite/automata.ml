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
(* removing automata statements *)
open Misc
open Location
open Ident
open Global
open Zelus
open Initial
open Deftypes

(* Automata must verify some well-formation constraints: *)
(* all branches going to a state must be of the same kind, that is, *)
(* being all by reset or continue, all strong or weak *)
(* Example of translation: *)
(* automaton
   | S1 -> locals in 
           do eq_list 
           until | c1 then do eq_list'1 in S'1(e1) | ... | ck then S'k(ek)
           unless | c'1 then do eq_list''1 in S''1(e'1) | ...
   | S2(p) -> ...p... | c2 then ...
   ...
   end

is translated into:

   (* strong preemption *)
   match pstate with
   | S1 -> present
           | c'1 -> eq_list''1 and state = S''1 and p1 = e'1 and res = true
           | ...
           end
   | S2 -> ...
   end

   (* weak preemption *)
   match state with
   | S1 -> reset
              locals
            and
              present
              | c1 -> eq_list1 and nstate = S'1 and p1 = e1 and nres = true
              | ...
              end
           every res or pres
   | S2 -> ...last p...
   end

   and pstate = pre(nstate) and pres = pre(nres)

2. Optimisations:
- no strong preemption : replace [res or pres] by [pres] and
   remove of the first pattern/matching
- no weak preemption: replace [res or pres] by [res] and
   remove of the control code [present ...]

3. Builds a local table table_of_types for every new type
*)

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

let emake desc ty = { e_desc = desc; e_loc = no_location; e_typ = ty }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty }
let eqmake desc = { eq_desc = desc; eq_loc = no_location }

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
  (* [n_to_parameters] associate a state name to a name in defs *)
  let states_and_variables_for_parameters s_h_list =
    let variable (states, n_to_parameters) { s_state = statepat } =
      match statepat.desc with
        | Estate0pat(n) -> n :: states, n_to_parameters
        | Estate1pat(n, p_list) ->
            n :: states, Env.add n p_list n_to_parameters in
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
  List.iter2 (fun n { info = v } -> Modules.add_constr (Ident.name n) v) states v_list;
  (* and the environment of state types *)
  TableOfTypes.add name typ_desc;
  (* compute the set of variables needed for storing parameters *)
  type_res, n_to_parameters

let cfalse = emake (Econst(Ebool(false))) Initial.typ_bool
let ctrue = emake (Econst(Ebool(true))) Initial.typ_bool
let var n ty = emake (Elocal(n)) ty
let last n ty = emake (Elast(n)) ty
let varpat n ty = pmake (Evarpat(n)) ty
let pair e1 e2 = 
  emake (Etuple([e1; e2])) 
    (Deftypes.make (Deftypes.Tproduct [e1.e_typ; e2.e_typ]))
let pairpat p1 p2 = 
  pmake (Etuplepat([p1; p2]))
    (Deftypes.make (Deftypes.Tproduct [p1.p_typ; p2.p_typ]))
    
let eq p e = eqmake (EQeq(p, e))
let eblock eq_list = 
  { b_vars = []; b_locals = []; b_body = eq_list; b_loc = no_location; 
    b_write = Total.empty; b_env = Env.empty }
let extend_block eq_list b_opt =
  match b_opt with
    | None -> eblock eq_list
    | Some(b) -> { b with b_body = eq_list @ b.b_body }
 
let reset b e = eqmake (EQreset(b, e))
let ematch e l = eqmake (EQmatch(ref true, e, l))
let present l default = eqmake (EQpresent(l, Some(default)))

let value ty = 
    { Deftypes.t_sort = Deftypes.Val; Deftypes.t_typ = ty }
let initialized is_init ty = 
    { Deftypes.t_sort = 
	Deftypes.Mem 
	  { Deftypes.discrete_memory with Deftypes.t_initialized = is_init };
      Deftypes.t_typ = ty }
    
(** Rename a pattern according to a renaming substitution *)
let rec rename r_env ({ p_desc = desc } as p) =
  let desc = match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> desc
    | Etuplepat(p_list) -> Etuplepat(List.map (rename r_env) p_list)
    | Evarpat(n) -> Evarpat(Env.find n r_env)
    | Erecordpat(label_pat_list) ->
      Erecordpat(List.map (fun (label, p) -> (label, rename r_env p)) 
                    label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraintpat(rename r_env p, ty)
    | Ealiaspat(p, n) -> Ealiaspat(rename r_env p, Env.find n r_env)
    | Eorpat(p1, p2) -> Eorpat(rename r_env p1, rename r_env p2) in
  { p with p_desc = desc }

(** returns [local x1,...,xn] from a typing env. [t1/x1,...,tn/xn] *)
let env_to_localvars env (x_list, t_env) =
  let add_local x t_entry (x_list, t_env) = 
    x :: x_list, Env.add x t_entry t_env in
  Env.fold add_local env (x_list, t_env)

let env_to_env acc env =
  let add x t_entry acc = Env.add x t_entry acc in
  Env.fold add env acc

(** Adds variables used for state parameters to the environment *)
let env_of_parameters env eq_list n_to_parameters s_h_list se_opt =
  (* test whether or not a state equals [se_opt] *)
  let equalstate se_opt { desc = desc } =
    match se_opt, desc with
       Some({ desc = Estate1(s1, _)}), Estate1pat(s2, _) when s1 = s2 -> true
      | _ -> false in
  (* extends the global environment [env] with parameters from the *)
  (* different state handlers. Every parameter becomes a state variable *)
  let entry is_init n { Deftypes.t_typ = ty } acc =
      (* set the kind of a variable to mustlast *)
      Env.add n (initialized is_init ty) acc in
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
          let pat_list = Env.find n n_to_parameters in
	  List.fold_left2 
	    (fun acc pat e -> eqmake (EQinit(pat, e, None)) :: acc) 
	    eq_list pat_list e_list in
  env, eq_list

(* an automaton may be a Moore automaton, i.e., with only weak transitions; *)
let moore s_h_list =
  let handler is_moore { s_unless = l } = is_moore && (l = []) in
    List.fold_left handler true s_h_list
      
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
let present_handlers body p_h_list =
  List.map
    (fun ({ p_body = b } as handler) -> { handler with p_body = body b })
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
    | EQreset(b, e) ->
        let b = block_eq_list b in
        env, { eq with eq_desc = EQreset(b, exp e) } :: eq_list
    | EQeq(pat, e) -> env, { eq with eq_desc = EQeq(pat, exp e) } :: eq_list
    | EQinit(pat, e0, e_opt) -> 
      env, 
      { eq with eq_desc = EQinit(pat, exp e0, optional_map exp e_opt) } :: eq_list
    | EQnext(pat, e, e0_opt) -> 
      env, 
      { eq with eq_desc = EQnext(pat, exp e, optional_map exp e0_opt) } :: eq_list
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
    | EQautomaton(state_handler_list, se_opt) ->
        automaton env eq_list state_handler_list se_opt

and equation_list env eq_list = List.fold_left equation (env, []) eq_list

and block_eq_list b =
  let locals l_list = List.map local l_list in
  let body eq_list = equation_list Env.empty eq_list in
  block locals body b

and present_handler_exp_list p_h_e_list =
  present_handlers exp p_h_e_list

and present_handler_block_eq_list p_h_b_eq_list =
  present_handlers block_eq_list p_h_b_eq_list

and match_handler_exp_list m_h_list =
  List.map 
    (fun ({ m_body = e } as handler) -> { handler with m_body = exp e }) m_h_list    

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
       
          
(** Translating an automaton *)
(** [eq_list] is a list of equations. The translation returns *)
(** an extended list containing [eq_list] and new equations *)
and automaton env eq_list handler_list se_opt =
  let moore = moore handler_list in

  (* introduce a sum type to represent states and *)
  (* build an environment which associate parameters to states *)
  let statetype, n_to_parameters = intro_type handler_list in

  (* for a parameterized state, generate [n = e] when calling the state *)
  (* adds equations [init n_1 = e_1 and ... and init n_k = e_k] *)
  (* for the initial state if it is entered with an initial value *)
  let env, eq_list = 
    env_of_parameters env eq_list n_to_parameters handler_list se_opt  in

  let longident n = Modules.longname(Ident.name n) in

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
    { p_desc = desc; p_loc = statepat.loc; p_typ = Deftypes.no_typ } in

  let translate_state { desc = desc; loc = loc } =
    match desc with
      | Estate0(n) -> 
          { e_desc = Econstr0(longident n);
            e_loc = loc;
            e_typ = Deftypes.no_typ }, []
      | Estate1(n, e_list) ->
          let pat_list = Env.find n n_to_parameters in
          { e_desc = Econstr0(longident n);
            e_loc = loc;
            e_typ = Deftypes.no_typ }, 
          List.map2 (fun pat e -> eqmake (EQeq(pat, e))) pat_list e_list in

  let cur_statename = Ident.fresh "s" in
  let cur_resetname = Ident.fresh "r" in
  let next_statename = Ident.fresh "ns" in
  let next_resetname = Ident.fresh "nr" in
  let pre_next_resetname = Ident.fresh "pnr" in
  let pre_next_statename = Ident.fresh "pns" in

  let statepat n = pmake (Evarpat(n)) statetype in
  let statevar n = var n statetype in
  let boolvar n = var n typ_bool in
  let boolpat n = pmake (Evarpat(n)) typ_bool in
  let fby_state initial e = 
    emake (Eapp(Efby, [emake (Econstr0(initial)) statetype; e])) statetype in
  let fby_false e = emake (Eapp(Efby, [cfalse; e])) Initial.typ_bool in

  (* [prestatename] is the target state computed by the previous *)
  (* weak action *)
  (* [preresetname] is the target reset condition computed by the *)
  (* previous weak action *)
  let strong prestatename preresetname { s_state = _; s_unless = su } =
    let default_cur_eq =
      [eq (statepat cur_statename) (statevar prestatename);
       eq (boolpat cur_resetname) (boolvar preresetname)] in
    let default_cur_present_handler =
      eblock default_cur_eq in
    let escape 
        { e_cond = e; e_reset = r; e_block = b_opt; 
          e_next_state = se; e_env = h0 } p_h_list =
      let se, eq_list_se = translate_state se in
      { p_cond = e;
        p_env = h0;
        p_body =
          (* by constrution, we know that equations on transitions [b_opt] *)
          (* are stateless thus no automaton can appear into them. *)
          (* No compilation is done for them *)
          extend_block
            ((eq (statepat cur_statename) se) ::
                (eq (boolpat cur_resetname) (if r then ctrue else cfalse))
              :: eq_list_se) b_opt } :: p_h_list in
    let cur_state_code =
      match su with
        | [] -> default_cur_eq
        | _ -> 
            let p_h_list = List.fold_right escape su [] in
            [present p_h_list default_cur_present_handler] in
      eblock 
        [reset (eblock cur_state_code) (boolvar preresetname)]
  in
    
  (* [statename] is the target state computed by the strong action         *)
  (* [resetname] is the target reset condition computed by strong action   *)
  let weak statename resetname { s_state = _; s_body = b; s_until = su } =
    let default_next_eq =
      [eq (statepat next_statename) (statevar statename);
       eq (boolpat next_resetname) cfalse] in
    let default_next_present_handler =
      eblock default_next_eq in
    let escape 
        { e_cond = e; e_reset = r; e_block = b_opt; e_next_state = se; e_env = h0 }
        p_h_list =
      let se, eq_list_se = translate_state se in
      { p_cond = e;
        p_env = h0;
        p_body =
          (* by constrution, we know that equations on transitions [b_opt] *)
          (* are stateless thus no automaton can appear into them. *)
          (* No compilation is done for them *)
          extend_block
            ((eq (statepat next_statename) se) ::
                (eq (boolpat next_resetname) (if r then ctrue else cfalse))
              :: eq_list_se) b_opt } :: p_h_list in
    let next_state_code =
      match su with
        | [] -> default_next_eq
        | _ -> 
            let p_h_list = List.fold_right escape su [] in
            [present p_h_list default_next_present_handler] in
    let b = block_eq_list b in
    let b = { b with b_body = next_state_code @ b.b_body } in
    eblock [reset b (boolvar resetname)] in

  (* the match/with code to compute the current active state *)
  let strong_handler prestatename preresetname =
    ematch (statevar prestatename)
      (List.map
          (fun ({ s_state = statepat } as case) ->
                { m_pat = translate_statepat statepat;
                  m_body = strong prestatename preresetname case;
                  m_env = Env.empty; m_reset = false })
          handler_list) in
    (* the match/with code to compute the next active state *)
  let weak_handler statename resetname =
    ematch (statevar statename)
      (List.map
          (fun ({ s_state = statepat } as case) ->
                { m_pat = translate_statepat statepat;
                  m_body = weak statename resetname case;
                  m_env = Env.empty; m_reset = false })
          handler_list) in
  (* the result *)
  let statetype_entry = value statetype in
  let typ_bool_entry = value typ_bool in
  Env.add cur_statename statetype_entry
    (Env.add next_statename statetype_entry
        (Env.add pre_next_statename statetype_entry
            (Env.add cur_resetname typ_bool_entry
                (Env.add next_resetname typ_bool_entry
                    (Env.add pre_next_resetname typ_bool_entry env))))),
  if moore then
    (eq (boolpat pre_next_resetname) (fby_false (boolvar (next_resetname)))) ::
      (eq (statepat pre_next_statename)
          (fby_state initial (statevar next_statename))) ::
      (weak_handler pre_next_statename pre_next_resetname) :: eq_list
  else
    (eq (boolpat pre_next_resetname) (fby_false (boolvar (next_resetname)))) ::
      (eq (statepat pre_next_statename)
          (fby_state initial (statevar next_statename))) ::
      (strong_handler pre_next_statename pre_next_resetname) ::
      (weak_handler cur_statename cur_resetname) :: eq_list

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
