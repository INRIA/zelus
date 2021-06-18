(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* rewrite the parging tree into an ast *)
(* that is, change [id: String.t] into [id: Ident.t] *)

open Parsetree
open Ident

module Error =
  struct
    type error =
      | Evar of string
      | Enon_linear_pat of string
      | Enon_linear_record of string
      | Enon_linear_automaton of string
      | Eautomaton_with_mixed_transitions
      | Emissing_in_orpat of string
                                                
    exception Err of Location.t * error
                     
    let error loc kind = raise (Err(loc, kind))
                       
    let message loc kind =
      begin match kind with
      | Evar(name) ->
         Format.eprintf "%aScoping error: The value identifier %s is unbound.@."
           Location.output_location loc name
      | Enon_linear_pat(name) ->
          Format.eprintf "%aScoping error: The variable %s is bound several \
                     times in this pattern.@."
            Location.output_location loc name
      | Enon_linear_record(name) ->
         Format.eprintf
           "%aScoping error: The label %s is defined several times.@."
            Location.output_location loc name
      | Emissing_in_orpat(name) ->
          Format.eprintf
            "%aScoping error: The variable %s must occur on both sides of \
               this pattern.@."
            Location.output_location loc name
      | Enon_linear_automaton(name) ->
          Format.eprintf
            "%aScoping error: the state %s is defined several times in \
               this automaton.@."
            Location.output_location loc name
      | Eautomaton_with_mixed_transitions ->
	 Format.eprintf
	   "%aScoping error: this automaton mixes weak and strong transitions.@."
	   Location.output_location loc
      end;
      raise Misc.Error 
end

module Env =
  struct
    include Map.Make(String)

    let append env0 env =
      fold (fun x v acc -> update x (function _ -> Some(v)) acc)
        env0 env
  end

module S = Set.Make (String)

let name loc env n =
  try
    Env.find n env
  with
  | Not_found -> Error.error loc (Error.Evar(n))

let shortname = function | Name(n) -> n | Modname({ id }) -> id
                                                            
let longname ln =
  match ln with
  | Name(s) -> Lident.Name(s)
  | Modname { qual; id } ->
     Lident.Modname { Lident.qual = qual; Lident.id = id }

(* compute the set of names defined by an equation *)
let rec buildeq defnames { desc } =
  match desc with
  | EQeq(pat, _) -> buildpat false defnames pat
  | EQreset(eq, _) -> buildeq defnames eq
  | EQand(and_eq_list) ->
     List.fold_left buildeq defnames and_eq_list
  | EQlocal(v_list, eq) ->
     let defnames_v_list = List.fold_left build_vardec S.empty v_list in
     let defnames_eq = buildeq S.empty eq in
     S.union defnames (S.diff defnames_eq defnames_v_list)
  | EQif(_, eq1, eq2) ->
     let defnames = buildeq defnames eq1 in
     buildeq defnames eq2
  | EQmatch(_, h_list) ->
     List.fold_left build_match_handler defnames h_list
  | EQpresent(p_h_list, b_opt) ->
     let defnames = 
       List.fold_left build_present_handler defnames p_h_list in
     let defnames =
       match b_opt with
       | NoDefault -> defnames
       | Init(eq) | Else(eq) -> buildeq defnames eq in
     defnames
  | EQautomaton(a_h_list, _) ->
     List.fold_left build_automaton_handler defnames a_h_list
  | EQempty ->  defnames
  | EQassert _ -> defnames
                
and build_vardec defnames { desc = { var_name } } = S.add var_name defnames

and build_match_handler defnames { desc = { m_body } } =
  buildeq defnames m_body

and build_present_handler defnames { desc = { p_body } } =
  buildeq defnames p_body
  
and build_state_name acc { desc; loc } =
  match desc with
  | Estate0pat(n) | Estate1pat(n, _) ->
     if Env.mem n acc then Error.error loc (Error.Enon_linear_automaton(n));
     let m = fresh n in
     Env.add n m acc

and build_automaton_handler defnames
  { desc = { s_vars; s_body; s_until; s_unless } } =
  let defnames_s_vars = List.fold_left build_vardec S.empty s_vars in
  let defnames_s_body = buildeq S.empty s_body in
  let defnames_s_trans =
    List.fold_left build_escape defnames_s_body s_until in
  let defnames_s_trans =
    List.fold_left build_escape defnames_s_trans s_unless in
  S.union defnames (S.diff defnames_s_trans defnames_s_vars)

and build_escape defnames { desc = { e_vars; e_body } } =
  let defnames_e_vars = List.fold_left build_vardec S.empty e_vars in
  let defnames_e_body = buildeq defnames e_body in
  S.union defnames (S.diff defnames_e_body defnames_e_vars)

(** Build a renaming environment **)
(* if [check_linear = true], stop when the same name appears twice *)
and buildpat check_linear defnames p =
  let rec build acc { desc } =
    match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> acc
    | Econstr1pat(_, p_list) | Etuplepat(p_list) ->
        build_list acc p_list
    | Evarpat(n) ->
	if S.mem n acc then 
        if check_linear 
        then Error.error p.loc (Error.Enon_linear_pat(n)) else acc
        else S.add n acc
    | Ealiaspat(p, n) ->
	let acc = build acc p in S.add n acc
    | Eorpat(p1, p2) -> 
	let orpat loc acc0 acc1 acc =
        let one key acc =
          if S.mem key acc1 then
            if S.mem key acc then
	      if check_linear 
              then Error.error loc (Error.Enon_linear_pat(key)) else acc
	      else S.add key acc
          else
	    Error.error loc (Error.Emissing_in_orpat(key)) in
        S.fold one acc0 acc in
        let acc1 = build S.empty p1 in
        let acc2 = build S.empty p2 in
        let acc = orpat p.loc acc1 acc2 acc in acc
    | Etypeconstraintpat(p, ty) -> build acc p
    | Erecordpat(l_p_list) -> build_record_list p.loc acc l_p_list
	
  and build_record_list loc acc label_pat_list =
    let rec buildrec acc labels label_pat_list =
      match label_pat_list with
      | [] -> acc
      | (lname, pat_label) :: label_pat_list ->
	  (* checks that the label appears only once *)
          let label = shortname lname in
          if S.mem label labels
          then Error.error loc (Error.Enon_linear_record(label))
          else
            buildrec (build acc pat_label) (S.add label labels)
              label_pat_list in
    buildrec acc S.empty label_pat_list
  and build_list acc p_list = 
    List.fold_left build acc p_list in
  build defnames p

let buildeq eq =
  let defnames = buildeq S.empty eq in
  S.fold (fun s acc -> let m = fresh s in Env.add s m acc) defnames Env.empty
  
              
let kind =
  function Kfun -> Zelus.Kfun | Knode -> Zelus.Knode | Kstatic -> Zelus.Kstatic

let immediate c =
  match c with
  | Eint(i) -> Zelus.Eint(i)
  | Ebool(b) -> Zelus.Ebool(b)
  | Efloat(f) -> Zelus.Efloat(f)
  | Evoid -> Zelus.Evoid
  | Estring(s) -> Zelus.Estring(s)
  | Echar(c) -> Zelus.Echar(c)
                
(* synchronous operators *)
let operator op =
  match op with
  | Efby -> Zelus.Efby
  | Eifthenelse -> Zelus.Eifthenelse
  | Eminusgreater -> Zelus.Eminusgreater
  | Eunarypre -> Zelus.Eunarypre
  | Eseq -> Zelus.Eseq
  | Erun(i) -> Zelus.Erun(i)
  | Eatomic -> Zelus.Eatomic  

(* translate types. *)
let rec types { desc; loc } =
  let desc = match desc with
    | Etypevar(n) -> Zelus.Etypevar(n)
    | Etypetuple(ty_list) -> Zelus.Etypetuple(List.map types ty_list)
    | Etypeconstr(lname, ty_list) ->
       Zelus.Etypeconstr(longname lname, List.map types ty_list)
    | Etypefun(k, ty_arg, ty_res) ->
       let ty_arg = types ty_arg in
       let ty_res = types ty_res in
       Zelus.Etypefun(kind k, ty_arg, ty_res) in
  { Zelus.desc = desc; Zelus.loc = loc }

(* make a block *)
let block loc s_vars s_eq =
  { Zelus.b_vars = s_vars; Zelus.b_body = s_eq;
    Zelus.b_loc = loc; Zelus.b_env = Ident.Env.empty;
    Zelus.b_write = Deftypes.empty }
  
(* [env_pat] is the environment for names that appear on the *)
(* left of a definition. [env] is for names that appear on the right *)
let rec equation env_pat env { desc; loc } =
  let eq_desc =
    match desc with
    | EQeq(pat, e) ->
       let pat = pattern_translate env_pat pat in
       let e = expression env e in
       Zelus.EQeq(pat, e)
    | EQreset(eq, e) ->
       let eq = equation env_pat env eq in
       let e = expression env e in
       Zelus.EQreset(eq, e)
    | EQand(and_eq_list) ->
       let and_eq_list = List.map (equation env_pat env) and_eq_list in
       Zelus.EQand(and_eq_list)
    | EQlocal(v_list, eq) ->
       let v_list, env_v_list = Util.mapfold (vardec env) Env.empty v_list in
       let env_pat = Env.append env_v_list env_pat in
       let env = Env.append env_v_list env in
       let eq = equation env_pat env eq in
       Zelus.EQlocal(block loc v_list eq)
    | EQif(e, eq1, eq2) ->
       let e = expression env e in
       let eq1 = equation env_pat env eq1 in
       let eq2 = equation env_pat env eq2 in
       Zelus.EQif(e, eq1, eq2)
    | EQmatch(e, m_h_list) ->
       let e = expression env e in
       let m_h_list = List.map (match_handler env_pat env) m_h_list in
       Zelus.EQmatch { is_total = false; e; handlers = m_h_list }
    | EQautomaton(a_h_list, st_opt) ->
       let is_weak, is_strong =
         List.fold_left
           (fun (is_weak, is_strong)
	        { desc = { s_until; s_unless } } ->
	     is_weak || (s_until <> []), is_strong || (s_unless <> []))
           (false, false) a_h_list in
       if is_weak && is_strong
       then Error.error loc (Error.Eautomaton_with_mixed_transitions)
       else
         let env_for_states =
           (* build the association table for state names *)
           List.fold_left
             (fun acc { desc = { s_state } } -> build_state_name acc s_state)
             Env.empty a_h_list in
         let handlers =
           List.map
             (automaton_handler is_weak env_for_states env_pat env) a_h_list in
         let state_opt =
           Util.optional_map (state env_for_states env) st_opt in
         Zelus.EQautomaton({ is_weak = true; handlers; state_opt })
    | EQempty ->
       Zelus. EQempty
    | EQassert(e) -> Zelus.EQassert(expression env e)
    | EQpresent(p_h_list, eq_opt) ->
       let handlers = List.map (present_handler env_pat env) p_h_list in
       let default_opt =
         match eq_opt with
         | NoDefault -> Zelus.NoDefault
         | Init(eq) -> Zelus.Init(equation env_pat env eq)
         | Else(eq) -> Zelus.Else(equation env_pat env eq) in
       Zelus.EQpresent({ handlers; default_opt }) in
  (* set the names defined in the equation *)
  { Zelus.eq_desc = eq_desc; Zelus.eq_write = Deftypes.empty;
    Zelus.eq_loc = loc }

and vardec env acc
{ desc = { var_name; var_init; var_default;
           var_typeconstraint; var_clock }; loc } =
  if Env.mem var_name acc then Error.error loc (Enon_linear_pat(var_name));
  let var_default =
    Util.optional_map (expression env) var_default in
  let var_init =
    Util.optional_map (expression env) var_init in
  let var_typeconstraint =
    Util.optional_map types var_typeconstraint in
  let m = Ident.fresh var_name in
  { Zelus.var_name = m; Zelus.var_init = var_init;
    Zelus.var_default = var_default;
    Zelus.var_typeconstraint = var_typeconstraint;
    Zelus.var_clock = var_clock; Zelus.var_loc = loc;
    Zelus.var_typ = Deftypes.no_typ },
  Env.add var_name m acc

and state env_for_states env { desc; loc } =
  let desc = match desc with
    | Estate0(f) ->
       let f = try Env.find f env_for_states 
               with | Not_found -> Error.error loc (Error.Evar(f)) in
       Zelus.Estate0(f)
  | Estate1(f, e_list) ->
     let f = try Env.find f env_for_states 
             with | Not_found -> Error.error loc (Error.Evar(f)) in
     let e_list = List.map (expression env) e_list in
     Zelus.Estate1(f, e_list)
  | Estateif(e, se1, se2) ->
     Zelus.Estateif(expression env e,
                    state env_for_states env se1,
                    state env_for_states env se2) in
  { Zelus.desc = desc; Zelus.loc = loc }

and statepat env_pat { desc; loc } =
  let desc, acc = match desc with
    | Estate0pat(f) ->
       let fm = try Env.find f env_pat
                with | Not_found -> Error.error loc (Error.Evar(f)) in
       Zelus.Estate0pat(fm), Env.empty
    | Estate1pat(f, n_list) ->
       let fm = try Env.find f env_pat
                with | Not_found -> Error.error loc (Error.Evar(f)) in
       let n_list, acc =
         Util.mapfold
           (fun acc n -> let m = Ident.fresh n in m, Env.add n m acc)
           Env.empty n_list in
     Estate1pat(fm, n_list), acc in
{ Zelus.desc = desc; Zelus.loc = loc }, acc

and present_handler env_pat env { desc = { p_cond; p_body }; loc } =
  let scpat, env_scpat = scondpat env p_cond in
  let env = Env.append env_scpat env in
  let p_body = equation env_pat env p_body in
  { Zelus.p_cond = scpat; Zelus.p_body = p_body; Zelus.p_loc = loc;
    Zelus.p_env = Ident.Env.empty }

and automaton_handler is_weak env_for_states env_pat env
  { desc = { s_state; s_vars; s_body; s_until; s_unless }; loc } =
  let s_state, env_s_state = statepat env_for_states s_state in
  let env = Env.append env_s_state env in
  let s_vars, env_s_vars = Util.mapfold (vardec env) Env.empty s_vars in
  let env_pat = Env.append env_s_vars env_pat in
  let env = Env.append env_s_vars env in
  let s_body = equation env_pat env s_body in
  let s_trans =
    List.map (escape env_for_states env_pat env)
      (if is_weak then s_until else s_unless) in
  { Zelus.s_state = s_state; Zelus.s_body = block loc s_vars s_body;
    Zelus.s_trans = s_trans; Zelus.s_loc = loc;
    Zelus.s_env = Ident.Env.empty;
    Zelus.s_reset = false }

and escape env_for_states env_pat env
  { desc = { e_reset; e_cond; e_vars; e_body; e_next_state }; loc } = 
  let e_cond, env_e_cond  = scondpat env e_cond in
  let env = Env.append env_e_cond env in
  let e_vars, env_e_vars = Util.mapfold (vardec env) Env.empty e_vars in
  let env_pat = Env.append env_e_vars env_pat in
  let env = Env.append env_e_vars env in
  let e_body = equation env_pat env e_body in
  let e_next_state = state env_for_states env e_next_state in
  { Zelus.e_reset; Zelus.e_cond = e_cond;
    Zelus.e_body = block loc e_vars e_body;
    Zelus.e_next_state = e_next_state; Zelus.e_loc = loc;
    Zelus.e_env = Ident.Env.empty }

and scondpat env scpat =
  (* first build the set of names *)
  let rec build_scondpat acc { desc; loc } =
    match desc with
    | Econdand(scpat1, scpat2) ->
        build_scondpat (build_scondpat acc scpat1) scpat2
    | Econdor(scpat1, scpat2) ->
       let orcond loc acc0 acc1 acc =
         let one key acc =
           if S.mem key acc1 then
	     if S.mem key acc then
	       Error.error loc (Error.Enon_linear_pat(key))
	     else S.add key acc
           else
	     Error.error loc (Error.Emissing_in_orpat(key)) in
         S.fold one acc0 acc in
       let acc1 = build_scondpat S.empty scpat1 in
       let acc2 = build_scondpat S.empty scpat2 in
       let acc = orcond loc acc1 acc2 acc in
       acc
    | Econdexp _ -> acc
    | Econdpat(_, p) -> buildpat true acc p
    | Econdon(scpat, _) -> build_scondpat acc scpat in
  (* rename *)
  let scondpat env_scpat env scpat =
    let rec scondpat { desc; loc } =
      let desc = match desc with
	| Econdand(scpat1, scpat2) ->
	   Zelus.Econdand(scondpat scpat1, scondpat scpat2)
	| Econdor(scpat1, scpat2) ->
	   Zelus.Econdor(scondpat scpat1, scondpat scpat2)
	| Econdexp(e) ->
           Zelus.Econdexp(expression env e)
	| Econdpat(e, p) ->
           Zelus.Econdpat(expression env e, pattern_translate env_scpat p)
	| Econdon(scpat, e) ->
           Zelus.Econdon(scondpat scpat, expression env e) in
      { Zelus.desc = desc; Zelus.loc = loc } in
    scondpat scpat in
  (* first build the environment for pattern variables *)
  let defnames = build_scondpat S.empty scpat in
  let env0 =
    S.fold
      (fun s acc -> let m = fresh s in Env.add s m acc) defnames Env.empty in
  (* translate *)
  let scpat = scondpat env0 env scpat in
  scpat, env0

and match_handler env_pat env { desc = { m_pat; m_body }; loc } = 
  let m_pat, env_m_pat = pattern env m_pat in
  let env = Env.append env_m_pat env in
  let m_body = equation env_pat env m_body in
  { Zelus.m_pat = m_pat; Zelus.m_body = m_body; Zelus.m_loc = loc;
    Zelus.m_env = Ident.Env.empty; Zelus.m_reset = false }

(** Patterns **)
and pattern_translate env { desc; loc } =
  let desc = match desc with
    | Ewildpat -> Zelus.Ewildpat
    | Econstpat(im) -> Zelus.Econstpat(immediate im)
    | Econstr0pat(ln) -> Zelus.Econstr0pat(longname ln)
    | Econstr1pat(ln, p_list) ->
       Zelus.Econstr1pat(longname ln, pattern_translate_list env p_list)
    | Etuplepat(p_list) -> Zelus.Etuplepat(pattern_translate_list env p_list)
    | Evarpat(n) -> Zelus.Evarpat(name loc env n)
    | Ealiaspat(p, n) ->
       Zelus.Ealiaspat(pattern_translate env p, name loc env n)
    | Eorpat(p1, p2) ->
       Zelus.Eorpat(pattern_translate env p1, pattern_translate env p2)
    | Etypeconstraintpat(p, ty) ->
       Zelus.Etypeconstraintpat(pattern_translate env p, types ty)
    | Erecordpat(l_p_list) ->
       Zelus.Erecordpat
         (List.map (fun (lname, p) -> (longname lname, pattern_translate env p))
	    l_p_list) in
  { Zelus.pat_desc = desc; Zelus.pat_loc = loc;
    Zelus.pat_typ = Deftypes.no_typ; Zelus.pat_caus = Defcaus.no_typ;
    Zelus.pat_init = Definit.no_typ }
  
and pattern_translate_list env p_list = List.map (pattern_translate env) p_list

(* Build the renaming environment then translate *)
and pattern env p =
  let defnames = buildpat true S.empty p in
  let env0 =
    S.fold
      (fun s acc -> let m = fresh s in Env.add s m acc) defnames Env.empty in
  pattern_translate env0 p, env0

and expression env { desc; loc } =
  let desc =
    match desc with
    | Evar(Name(n)) ->
       begin try
           let m = Env.find n env in
           Zelus.Elocal(m)
         with
         | Not_found ->
            Zelus.Eglobal({ lname = Name(n);
                          typ_instance = Deftypes.no_typ_instance })
       end
    | Evar(Modname _ as ln) ->
       Zelus.Eglobal({ lname = longname ln;
                     typ_instance = Deftypes.no_typ_instance })
    | Econst(c) -> Zelus.Econst(immediate c)
    | Econstr0(f) -> Zelus.Econstr0 { lname = longname f }
    | Econstr1(f, e_list) ->
       Zelus.Econstr1
         { lname = longname f; arg_list = List.map (expression env) e_list }
    | Elast(x) ->
       let x = try Env.find x env
               with | Not_found -> Error.error loc (Error.Evar(x)) in
       Zelus.Elast(x)
    | Eop(op, e_list) ->
       let e_list = List.map (expression env) e_list in
       Zelus.Eop(operator op, e_list)
    | Etuple(e_list) ->
       let e_list = List.map (expression env) e_list in
       Zelus.Etuple(e_list)
    | Elet(is_rec, eq, e) ->
       let env_pat = buildeq eq in
       let env_let = Env.append env_pat env in
       let eq = equation env_pat (if is_rec then env_let else env) eq in
       let e = expression env_let e in
       Zelus.Elet({ l_rec = is_rec; l_eq = eq; l_loc = loc;
                    l_env = Ident.Env.empty }, e)
    | Eapp(f, arg_list) ->
       let f = expression env f in
       let arg_list = List.map (expression env) arg_list in
       Zelus.Eapp(f, arg_list)
    | Erecord_access(e, lname) ->
       let e = expression env e in
       Zelus.Erecord_access { arg = e; label = longname lname }
    | Erecord(label_e_list) ->
       Zelus.Erecord(recordrec loc env label_e_list)
    | Erecord_with(e, label_e_list) ->
       Zelus.Erecord_with(expression env e, recordrec loc env label_e_list)
    | Etypeconstraint(e, texp) ->
       Zelus.Etypeconstraint(expression env e, types texp)
    | Efun(fd) -> Zelus.Efun(funexp env fd) in
  { Zelus.e_desc = desc; Zelus.e_loc = loc;
    Zelus.e_typ = Deftypes.no_typ; Zelus.e_caus = Defcaus.no_typ;
    Zelus.e_init = Definit.no_typ }

and recordrec loc env label_e_list =
  (* check that a label name appear only once *)
  let rec recordrec labels label_e_list =
    match label_e_list with
    | [] -> []
    | (lname, e) :: label_e_list ->
       (* check that labels are all different *)
       let l = shortname lname in
       if S.mem l labels
       then Error.error loc (Error.Enon_linear_record(l))
       else { Zelus.label = longname lname; Zelus.arg = expression env e } ::
              recordrec (S.add l labels) label_e_list in
  recordrec S.empty label_e_list

and funexp env { desc = { f_kind; f_atomic; f_args; f_body }; loc } =
  let f_args, env_f_args = Util.mapfold (arg env) Env.empty f_args in
  let env = Env.append env_f_args env in
  let f_body = result env f_body in
  { Zelus.f_kind = kind f_kind; Zelus.f_atomic = f_atomic;
    Zelus.f_args = f_args; Zelus.f_body = f_body; Zelus.f_loc = loc;
    Zelus.f_env = Ident.Env.empty }

and arg env acc v_list = Util.mapfold (vardec env) acc v_list

and result env { desc; loc } =
  let r_desc =
    match desc with
    | Exp(e) -> Zelus.Exp(expression env e)
    | Returns(v_list, eq) ->
       let v_list, env_v_list = Util.mapfold (vardec env) Env.empty v_list in
       let env = Env.append env_v_list env in
       let eq = equation env_v_list env eq in
       Zelus.Returns(block loc v_list eq) in
  { r_desc; r_loc = loc; r_typ = Deftypes.no_typ;
    r_caus = Defcaus.no_typ; r_init = Definit.no_typ}
  
(* type declarations. *)
let rec type_decl { desc; loc } =
  let desc = match desc with
  | Eabstract_type -> Zelus.Eabstract_type
  | Eabbrev(ty) -> Zelus.Eabbrev(types ty)
  | Evariant_type(constr_decl_list) ->
      Zelus.Evariant_type(List.map constr_decl constr_decl_list)
  | Erecord_type(n_ty_list) ->
      Zelus.Erecord_type
        (List.map (fun (n, ty) -> (n, types ty)) n_ty_list) in
  { Zelus.desc = desc; Zelus.loc = loc }

and constr_decl { desc; loc } =
  let desc = match desc with
  | Econstr0decl(n) -> Zelus.Econstr0decl(n)
  | Econstr1decl(n, ty_list) ->
      Zelus.Econstr1decl(n, List.map types ty_list) in
  { Zelus.desc = desc; Zelus.loc = loc }

let type_decls n_params_typdecl_list =
  List.map (fun (n, pars, typdecl) -> (n, pars, type_decl typdecl))
    n_params_typdecl_list

let implementation { desc; loc } =
  try
    let desc = match desc with
      | Eopen(n) -> Zelus.Eopen(n)
      | Eletdecl(f, e) ->
         let e = expression Env.empty e in
         Zelus.Eletdecl(f, e)
      | Etypedecl(f, params, td) ->
         let td = type_decl td in
         Zelus.Etypedecl(f, params, td) in
    { Zelus.desc = desc; Zelus.loc = loc }
  with
    Error.Err(loc, kind) -> Error.message loc kind
                          
let program i_list = List.map implementation i_list

let interface interf =
  try
    let desc = match interf.desc with
      | Einter_open(n) -> Zelus.Einter_open(n)
      | Einter_typedecl(n, params, tydecl) ->
          Zelus.Einter_typedecl(n, params, type_decl tydecl)
      | Einter_constdecl(n, typ, l) ->
          Zelus.Einter_constdecl(n, types typ, l) in
      { Zelus.desc = desc; Zelus.loc = interf.loc }
  with
    | Error.Err(loc, err) -> Error.message loc err

let interface_list inter_list = Util.iter interface inter_list
