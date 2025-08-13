(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2025 Inria Paris                                          *)
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
      | Enon_linear_forloop of string
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
      | Enon_linear_forloop(name) ->
          Format.eprintf
	    "%aScoping error: The variable %s is bound several times \
               in this loop.@."
            Location.output_location loc name
      | Eautomaton_with_mixed_transitions ->
	 Format.eprintf
	   "%aScoping error: this automaton mixes weak \
            and strong transitions.@."
	   Location.output_location loc
      end;
      raise Misc.Error 
end

module S = Set.Make (String)

module Env =
  struct
    include Map.Make(String)

    (* update an environment *)
    let append env0 env =
      fold (fun x v acc -> update x (function _ -> Some(v)) acc)
        env0 env

    (* makes a renaming for a set of names *)
    let make defnames env =
      S.fold (fun s acc -> let m = fresh s in add s m acc) defnames env
  end

module type INFO =
  sig
    type info
    val no_info : info
    val print: Format.formatter -> info -> unit
  end

module Make (Info: INFO) =
  struct
    (* make a block *)
    let make_block loc s_vars s_eq =
      { Zelus.b_vars = s_vars; Zelus.b_body = s_eq;
        Zelus.b_loc = loc; Zelus.b_write = Defnames.empty;
        Zelus.b_env = Ident.Env.empty }
    
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
    
    
    let vkind =
      function
      | Kconst -> Zelus.Kconst
      | Kstatic -> Zelus.Kstatic
      | Kany -> Zelus.Kany
    
    let tkind =
      function
      | Kdiscrete -> Zelus.Kdiscrete | Kcont -> Zelus.Kcont
    
    let kind =
      function
      | Kfun(v) -> Zelus.Kfun(vkind v)
      | Knode(t) -> Zelus.Knode(tkind t)
    
    let immediate c =
      match c with
      | Eint(i) -> Zelus.Eint(i)
      | Ebool(b) -> Zelus.Ebool(b)
      | Efloat(f) -> Zelus.Efloat(f)
      | Evoid -> Zelus.Evoid
      | Estring(s) -> Zelus.Estring(s)
      | Echar(c) -> Zelus.Echar(c)
    
    (* synchronous operators *)
    let rec operator op =
      match op with
      | Efby -> Zelus.Efby
      | Eifthenelse -> Zelus.Eifthenelse
      | Eminusgreater -> Zelus.Eminusgreater
      | Eunarypre -> Zelus.Eunarypre
      | Eseq -> Zelus.Eseq
      | Erun(i) -> Zelus.Erun(i)
      | Eatomic -> Zelus.Eatomic  
      | Etest -> Zelus.Etest
      | Eup -> Zelus.Eup { is_zero = true }
      | Einitial -> Zelus.Einitial
      | Edisc -> Zelus.Edisc
      | Eperiod -> Zelus.Eperiod
      | Ehorizon -> Zelus.Ehorizon { is_zero = true }
      | Earray(op) -> Zelus.Earray(array_operator op)
    
    and array_operator op =
      match op with
      | Eget -> Zelus.Eget
      | Eupdate -> Zelus.Eupdate
      | Eget_with_default -> Zelus.Eget_with_default
      | Eslice -> Zelus.Eslice
      | Econcat -> Zelus.Econcat
      | Earray_list -> Zelus.Earray_list
      | Etranspose -> Zelus.Etranspose
      | Ereverse -> Zelus.Ereverse
      | Eflatten -> Zelus.Eflatten
      | Emake -> Zelus.Emake
    
    (* translate types. [env] is used to renames dependent variables *)
    let rec types env { desc; loc } =
      let desc = match desc with
        | Etypevar(n) -> Zelus.Etypevar(n)
        | Etypetuple(ty_list) -> Zelus.Etypetuple(List.map (types env) ty_list)
        | Etypeconstr(lname, ty_list) ->
           Zelus.Etypeconstr(longname lname, List.map (types env) ty_list)
        | Etypefun(k, n_opt, ty_arg, ty_res) ->
           let ty_arg = types env ty_arg in
           let n_opt, env =
	     match n_opt with
	     | None -> None, env
	     | Some(n) ->
                let m = fresh n in Some(m), Env.add n m env in
           let ty_res = types env ty_res in
           Zelus.Etypefun
             { ty_kind = kind k; ty_name_opt = n_opt; ty_arg; ty_res }
        | Etypevec(ty_arg, si) ->
           Zelus.Etypevec(types env ty_arg, size env si) in
      { Zelus.desc = desc; Zelus.loc = loc }
    
    (* size expressions *)
    and size env { desc; loc } =
      let operator =
        function
        | Size_plus -> Zelus.Size_plus | Size_minus -> Zelus.Size_minus
        | Size_mult -> Zelus.Size_mult in
      let desc = match desc with
        | Size_int(i) -> Zelus.Size_int(i)
        | Size_frac(s, q) -> Zelus.Size_frac { num = size env s; denom = q }
        | Size_var(n) -> Zelus.Size_var(name loc env n)
        | Size_op(op, s1, s2) ->
           Zelus.Size_op(operator op, size env s1, size env s2) in
      { desc; loc }
    
    (** Build a renaming environment **)
    (* if [check_linear = true], stop when the same name appears twice *)
    let buildpat check_linear defnames p =
      let rec build acc { desc } =
        match desc with
        | Ewildpat | Econstpat _ | Econstr0pat _ -> acc
        | Econstr1pat(_, p_list) | Etuplepat(p_list) | Earraypat(p_list) ->
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
    
    (* compute the set of names defined by an equation *)
    let rec buildeq defnames { desc } =
      match desc with
      | EQeq(pat, _) -> buildpat false defnames pat
      | EQsizefun(x, _, _) | EQder(x, _, _, _) | EQinit(x, _) | EQemit(x, _) -> 
         S.add x defnames
      | EQreset(eq, _) -> buildeq defnames eq
      | EQand(and_eq_list) ->
         List.fold_left buildeq defnames and_eq_list
      | EQlocal(v_list, eq) ->
         let defnames_v_list = List.fold_left build_vardec S.empty v_list in
         let defnames_eq = buildeq S.empty eq in
         S.union defnames (S.diff defnames_eq defnames_v_list)
      | EQlet(_, eq) -> buildeq defnames eq
      | EQif(_, eq1, eq2) ->
         let defnames = buildeq defnames eq1 in
         buildeq defnames eq2
      | EQmatch(_, _, h_list) ->
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
      | EQforloop({ for_body }) -> build_for_body_eq defnames for_body
    
    and build_vardec defnames { desc = { var_name }; loc } =
      if S.mem var_name defnames
      then Error.error loc (Enon_linear_pat(var_name));
      S.add var_name defnames
    
    and build_for_vardec defnames { desc = { for_vardec } } =
      build_vardec defnames for_vardec
    
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
    
    and build_block defnames { desc = { b_vars; b_body }; loc } =
      let bounded_names = List.fold_left build_vardec S.empty b_vars in
      let defnames_body = buildeq S.empty b_body in
      bounded_names, S.union defnames (S.diff defnames_body bounded_names)
    
    and build_automaton_handler defnames
{ desc = { s_body; s_until; s_unless } } =
      let bounded_names, defnames_s_body = build_block S.empty s_body in
      let defnames_s_trans =
        List.fold_left build_escape defnames_s_body s_until in
      let defnames_s_trans =
        List.fold_left build_escape defnames_s_trans s_unless in
      S.union defnames (S.diff defnames_s_trans bounded_names)
    
    and build_escape defnames { desc = { e_body } } =
      let _, defnames_e_body = build_block S.empty e_body in
      S.union defnames defnames_e_body
    
    and build_for_body_eq defnames { for_out; for_block } =
      (* [xi [init e] [default e]] means that [xi] is defined by the for loop *)
      (* and visible outside of it. On the contrary *)
      (* [xi [init e] [default e] out x] means that [xi] stay local and *)
      (* [x] is defined by the for loop and visible outside of it *)
      let build_for_out
            (acc_left, acc_right) { desc = { for_name; for_out_name } } =
        match for_out_name with
        | None -> acc_left, acc_right
        | Some(x) -> S.add for_name acc_left, S.add x acc_right in
      let acc_left, acc_right =
        List.fold_left build_for_out (S.empty, S.empty) for_out in
      
      (* computes defnames for the block *)
      let _, defnames_body = build_block defnames for_block in
      S.union defnames
        (S.union (* remove [xi] in defnames *)
           (S.diff defnames_body acc_left) acc_right)
    
    let buildeq eq =
      let defnames = buildeq S.empty eq in
      Env.make defnames Env.empty
    
    (* Patterns *)
    let rec pattern_translate env { desc; loc } =
      let desc = match desc with
        | Ewildpat -> Zelus.Ewildpat
        | Econstpat(im) -> Zelus.Econstpat(immediate im)
        | Econstr0pat(ln) -> Zelus.Econstr0pat(longname ln)
        | Econstr1pat(ln, p_list) ->
           Zelus.Econstr1pat(longname ln, pattern_translate_list env p_list)
        | Etuplepat(p_list) ->
           Zelus.Etuplepat(pattern_translate_list env p_list)
        | Evarpat(n) -> Zelus.Evarpat(name loc env n)
        | Ealiaspat(p, n) ->
           Zelus.Ealiaspat(pattern_translate env p, name loc env n)
        | Eorpat(p1, p2) ->
           Zelus.Eorpat(pattern_translate env p1, pattern_translate env p2)
        | Etypeconstraintpat(p, ty) ->
           Zelus.Etypeconstraintpat(pattern_translate env p, types env ty)
        | Erecordpat(l_p_list) ->
           Zelus.Erecordpat
             (List.map (fun (lname, p) ->
                  { Zelus.label = longname lname;
                    Zelus.arg = pattern_translate env p })
	        l_p_list)
        | Earraypat(p_list) ->
           Zelus.Earraypat(pattern_translate_list env p_list) in
      { Zelus.pat_desc = desc; Zelus.pat_loc = loc;
        Zelus.pat_info = Info.no_info }
    
    and pattern_translate_list env p_list =
      List.map (pattern_translate env) p_list
    
    (* Build the renaming environment then translate *)
    and pattern env p =
      let defnames = buildpat true S.empty p in
      let env0 = Env.make defnames Env.empty in
      pattern_translate env0 p, env0
    
    let present_handler scondpat body env { desc = { p_cond; p_body }; loc } =
      let scpat, env_scpat = scondpat env p_cond in
      let env = Env.append env_scpat env in
      let p_body = body env p_body in
      { Zelus.p_cond = scpat; Zelus.p_body = p_body; Zelus.p_loc = loc; 
        Zelus.p_zero = false; Zelus.p_env = Ident.Env.empty }
    
    let match_handler body env { desc = { m_pat; m_body }; loc } = 
      let m_pat, env_m_pat = pattern env m_pat in
      let env = Env.append env_m_pat env in
      let m_body = body env m_body in
      { Zelus.m_pat = m_pat; Zelus.m_body = m_body; Zelus.m_loc = loc;
        Zelus.m_reset = false; Zelus.m_zero = false;
        Zelus.m_env = Ident.Env.empty }
    
    (* [env_pat] is the environment for names that appear on the *)
    (* left of a definition. [env] is for names that appear on the right *)
    let rec equation env_pat env { desc; loc } =
      let eq_desc =
        match desc with
        | EQeq(pat, e) ->
           let pat = pattern_translate env_pat pat in
           let e = expression env e in
           Zelus.EQeq(pat, e)
        | EQsizefun(x, x_list, e) ->
           let x = name loc env_pat x in
           (* build the renaming *)
           let x_list, x_env = 
             Util.mapfold 
               (fun acc n ->
                 if Env.mem n acc 
                 then Error.error loc (Error.Enon_linear_pat(n))
                 else let m = fresh n in m, Env.add n m acc) Env.empty x_list in
           let env = Env.append x_env env in
           Zelus.EQsizefun
             { sf_id = x; sf_id_list = x_list; sf_e = expression env e;
               sf_loc = loc; sf_env = Ident.Env.empty }
        | EQder(x, e, e_opt, p_h_list) ->
           Zelus.EQder
             { id = name loc env_pat x; e = expression env e;
               e_opt = Util.optional_map (expression env) e_opt;
               handlers = 
                 List.map
                   (present_handler scondpat expression env) p_h_list }
        | EQinit(x, e) -> EQinit(name loc env_pat x, expression env e)
        | EQemit(x, e_opt) ->
           EQemit(name loc env_pat x, Util.optional_map (expression env) e_opt)
        | EQreset(eq, e) ->
           let eq = equation env_pat env eq in
           let e = expression env e in
           Zelus.EQreset(eq, e)
        | EQand(eq_list) ->
           let eq_list = List.map (equation env_pat env) eq_list in
           Zelus.EQand { ordered = false; eq_list }
        | EQlocal(v_list, eq) ->
           let v_list, env_v_list = vardec_list env v_list in
           let env_pat = Env.append env_v_list env_pat in
           let env = Env.append env_v_list env in
           let eq = equation env_pat env eq in
           Zelus.EQlocal(make_block loc v_list eq)
        | EQlet(l_eq, in_eq) ->
           let l_eq, env = letin env l_eq in
           let in_eq = equation env_pat env in_eq in
           Zelus.EQlet(l_eq, in_eq)
        | EQif(e, eq_true, eq_false) ->
           let e = expression env e in
           let eq_true = equation env_pat env eq_true in
           let eq_false = equation env_pat env eq_false in
           Zelus.EQif { e; eq_true; eq_false }
        | EQmatch(is_size, e, m_h_list) ->
           let e = expression env e in
           let m_h_list =
             List.map (match_handler (equation env_pat) env) m_h_list in
           Zelus.EQmatch { is_size; is_total = false; e; handlers = m_h_list }
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
                 (fun acc { desc = { s_state } } ->
                   build_state_name acc s_state)
                 Env.empty a_h_list in
             let handlers =
               List.map
                 (automaton_handler is_weak env_for_states env_pat env)
                 a_h_list in
             let state_opt =
               Util.optional_map (state env_for_states env) st_opt in
             Zelus.EQautomaton({ is_weak; handlers; state_opt })
        | EQempty ->
           Zelus. EQempty
        | EQassert(e_body) ->
           Zelus.EQassert
             { Zelus.a_body = expression env e_body;
               Zelus.a_hidden_env = Ident.Env.empty;
               Zelus.a_free_vars = Ident.S.empty }
        | EQpresent(p_h_list, eq_opt) ->
           let handlers =
             List.map
               (present_handler scondpat (equation env_pat) env) p_h_list in
           let default_opt =
             match eq_opt with
             | NoDefault -> Zelus.NoDefault
             | Init(eq) -> Zelus.Init(equation env_pat env eq)
             | Else(eq) -> Zelus.Else(equation env_pat env eq) in
           Zelus.EQpresent({ handlers; default_opt })
        | EQforloop(f) ->
           Zelus.EQforloop(forloop_eq env_pat env f)
      in
      (* set the names defined in the equation *)
      { Zelus.eq_desc = eq_desc; Zelus.eq_write = Defnames.empty;
        Zelus.eq_loc = loc; Zelus.eq_safe = true; Zelus.eq_index = -1 }
    
    and trans_for_input env acc i_list =
      let input acc { desc; loc } =
        let desc, acc = match desc with
          | Einput { id; e; by } ->
             if Env.mem id acc
             then Error.error loc (Error.Enon_linear_forloop(id))
             else
               let m = fresh id in
               let e = expression env e in
               let by = Util.optional_map (expression env) by in
               Zelus.Einput { id = m; e; by }, Env.add id m acc
          | Eindex { id; e_left; e_right; dir } ->
             if Env.mem id acc
             then Error.error loc (Error.Enon_linear_forloop(id))
             else
               let m = fresh id in
               let e_left = expression env e_left in
               let e_right = expression env e_right in
               Zelus.Eindex { id = m; e_left; e_right; dir },
               Env.add id m acc in
        { Zelus.desc = desc; Zelus.loc = loc }, acc in
      Util.mapfold input acc i_list
    
    and trans_for_out env i_env for_out =
      (* [local_out_env] is the environment for variables defined in the *)
      (* for loop that are associated to an output [xi out x]. In that *)
      (* case, [xi] is local to the loop body; [x] is the only visible *)
    (* defined variable otherwise, [xi] is defined by the for loop *)
    (* and visible outside of it *)
      let for_out_one local_out_env
            { desc = { for_name; for_init; for_default; for_out_name }; loc } =
        (* check that output name [xi] is distinct from input names. This is *)
        (* not mandatory but makes loops simpler to understand *)
        if Env.mem for_name i_env
        then Error.error loc (Enon_linear_pat(for_name));
        let for_name, local_out_env =
          match for_out_name with
          | None -> name loc env for_name, local_out_env
          | Some(x) -> let m = fresh for_name in
                       m, Env.add for_name m local_out_env in
        let for_init =
          Util.optional_map (expression env) for_init in
        let for_default =
          Util.optional_map (expression env) for_default in
        let for_out_name = Util.optional_map (name loc env) for_out_name in
        { Zelus.desc =
            { Zelus.for_name = for_name; Zelus.for_init = for_init;
              Zelus.for_default = for_default;
              Zelus.for_out_name = for_out_name;
              Zelus.for_info = Info.no_info  };
          Zelus.loc = loc },
        local_out_env in
      Util.mapfold for_out_one Env.empty for_out
    
    (* translation of for loops *)
    and forloop_eq env_pat env
{ for_size; for_kind; for_index; for_input; for_resume;
  for_body = { for_out; for_block } } =
      let for_size = Util.optional_map (expression env) for_size in
      let for_index, i_env =
        match for_index with
        | None -> None, Env.empty
        | Some(id) -> let m = fresh id in Some(m), Env.singleton id m in
      let for_input, i_env =
        trans_for_input env i_env for_input in
      let env = Env.append i_env env in
      let for_out, local_out_env =
        trans_for_out env i_env for_out in
      let env = Env.append local_out_env env in
      let env_pat = Env.append local_out_env env in
      let env_body, for_block = block equation env_pat env for_block in
      let for_kind =
        match for_kind with
        | Kforeach -> Zelus.Kforeach
        | Kforward(e_opt) ->
           Zelus.Kforward(Util.optional_map (exit_expression env_body) e_opt) in
      { Zelus.for_size = for_size;
        Zelus.for_kind = for_kind;
        Zelus.for_index = for_index;
        Zelus.for_input = for_input;
        Zelus.for_body = { for_out; for_block; for_out_env = Ident.Env.empty };
        Zelus.for_resume = for_resume;
        Zelus.for_env = Ident.Env.empty }
    
    (** Translating a sequence of local declarations *)
    and leqs env l = Util.mapfold letin env l
    
    and letin env { desc = { l_kind; l_rec; l_eq }; loc } =
      let env_pat = buildeq l_eq in
      let new_env = Env.append env_pat env in
      let l_eq = equation env_pat (if l_rec then new_env else env) l_eq in
      let l_kind = vkind l_kind in
      { l_kind; l_rec; l_eq; l_loc = loc; l_env = Ident.Env.empty }, new_env
    
    and vardec env { desc = { var_name; var_init; var_default;
                              var_typeconstraint; var_clock; var_is_last };
                     loc } =
      let var_default =
        Util.optional_map (expression env) var_default in
      let var_init =
        Util.optional_map (expression env) var_init in
      let var_typeconstraint =
        Util.optional_map (types env) var_typeconstraint in
      let m = name loc env var_name in
      { Zelus.var_name = m; Zelus.var_init = var_init;
        Zelus.var_default = var_default;
        Zelus.var_typeconstraint = var_typeconstraint;
        Zelus.var_clock = var_clock; Zelus.var_loc = loc;
        Zelus.var_is_last = var_is_last;
        Zelus.var_init_in_eq = false;
        Zelus.var_info = Info.no_info }
    
    (* treat a list of variable declarations *)
    (*- computes the list of names;
     *- builds an initial environment;
     *- apply the substitution; 
     *- the two steps is necessary because 
     *- [local x init y, y init x do ... x = ... and y = ... done]
     *- is corrects and a short-cut for 
     *- [local last x, last y do last x = y and last y = x and ... done] *)
    and vardec_list env v_list =
      let defnames = List.fold_left build_vardec S.empty v_list in
      let env_v_list = Env.make defnames Env.empty in
      let env = Env.append env_v_list env in
      let v_list = List.map (vardec env) v_list in
      v_list, env_v_list 
    
    and for_vardec env { desc = { for_array; for_vardec }; loc } =
      let for_vardec = vardec env for_vardec in
      { Zelus.desc = { Zelus.for_array = for_array;
                       Zelus.for_vardec = for_vardec };
        Zelus.loc = loc }
    
    and for_vardec_list env for_v_list =
      let defnames = List.fold_left build_for_vardec S.empty for_v_list in
      let env_v_list = Env.make defnames Env.empty in
      let env = Env.append env_v_list env in
      let v_list = List.map (for_vardec env) for_v_list in
      v_list, env_v_list
    
    (* [local x1 [init e1][default e'1],...,xn[...] do eq] *)
    and block body env_pat env { desc = { b_vars; b_body }; loc } =
      let b_vars, env_b_vars = vardec_list env b_vars in
      let env_pat = Env.append env_b_vars env_pat in
      let env = Env.append env_b_vars env in
      let b = body env_pat env b_body in
      env, { Zelus.b_vars = b_vars; Zelus.b_body = b; Zelus.b_loc = loc;
             Zelus.b_write = Defnames.empty; Zelus.b_env = Ident.Env.empty }
    
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
    
    
    and automaton_handler is_weak env_for_states env_pat env
           { desc = { s_state; s_let; s_body; s_until; s_unless }; loc } =
      let s_state, env_s_state = statepat env_for_states s_state in
      let env_pat = Env.append env_s_state env_pat in
      let env = Env.append env_s_state env in
      let s_let, env = leqs env s_let in
      let env, s_body = block equation env_pat env s_body in
      let s_trans =
        List.map (escape env_for_states env_pat env)
          (if is_weak then s_until else s_unless) in
      { Zelus.s_state = s_state; Zelus.s_let = s_let; Zelus.s_body = s_body;
        Zelus.s_trans = s_trans; Zelus.s_loc = loc; Zelus.s_reset = false; 
        Zelus.s_env = Ident.Env.empty }
    
    and escape env_for_states env_pat env
            { desc = { e_reset; e_cond; e_let; e_body; e_next_state }; loc } = 
      let e_cond, env_e_cond  = scondpat env e_cond in
      let env_pat = Env.append env_e_cond env_pat in
      let env = Env.append env_e_cond env in
      let e_let, env = leqs env e_let in
      let env, e_body = block equation env_pat env e_body in
      let e_next_state = state env_for_states env e_next_state in
      { Zelus.e_reset; Zelus.e_cond = e_cond; Zelus.e_let = e_let;
        Zelus.e_body = e_body; Zelus.e_next_state = e_next_state;
        Zelus.e_loc = loc; Zelus.e_env = Ident.Env.empty; e_zero = false; }
    
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
      let env0 = Env.make defnames Env.empty in
      (* translate *)
      let scpat = scondpat env0 env scpat in
      scpat, env0
    
    and expression env { desc; loc } =
      let desc =
        match desc with
        | Evar(Name(n)) ->
           begin try
               let m = Env.find n env in
               Zelus.Evar(m)
             with
             | Not_found ->
                Zelus.Eglobal({ lname = Name(n) })
           end
        | Evar(Modname _ as ln) ->
           Zelus.Eglobal({ lname = longname ln })
        | Econst(c) -> Zelus.Econst(immediate c)
        | Econstr0(f) -> Zelus.Econstr0 { lname = longname f }
        | Econstr1(f, e_list) ->
           Zelus.Econstr1
             { lname = longname f; arg_list = List.map (expression env) e_list }
        | Elast(copy, x) ->
           let id = try Env.find x env
                    with | Not_found -> Error.error loc (Error.Evar(x)) in
           Zelus.Elast { copy; id }
        | Eop(op, e_list) ->
           let e_list = List.map (expression env) e_list in
           Zelus.Eop(operator op, e_list)
        | Etuple(e_list) ->
           let e_list = List.map (expression env) e_list in
           Zelus.Etuple(e_list)
        | Elet(leq, e) ->
           let leq, new_env = letin env leq in
           let e = expression new_env e in
           Zelus.Elet(leq, e)
        | Elocal(v_list, eq, e) ->
           let v_list, env_v_list = vardec_list env v_list in
           let env_pat = env_v_list in
           let env = Env.append env_v_list env in
           let eq = equation env_pat env eq in
           let e = expression env e in
           Zelus.Elocal(make_block loc v_list eq, e)
        | Eapp(is_inline, f, arg_list) ->
           let f = expression env f in
           let arg_list = List.map (expression env) arg_list in
           Zelus.Eapp { is_inline; f; arg_list }
        | Esizeapp(f, size_list) ->
           Zelus.Esizeapp 
             { f = expression env f; size_list = List.map (size env) size_list }
        | Erecord_access(e, lname) ->
           let e = expression env e in
           Zelus.Erecord_access { arg = e; label = longname lname }
        | Erecord(label_e_list) ->
           Zelus.Erecord(recordrec loc env label_e_list)
        | Erecord_with(e, label_e_list) ->
           Zelus.Erecord_with(expression env e, recordrec loc env label_e_list)
        | Etypeconstraint(e, texp) ->
           Zelus.Etypeconstraint(expression env e, types env texp)
        | Efun(fd) -> Zelus.Efun(funexp env fd)
        | Ematch(is_size, e, m_h_list) ->
           let e = expression env e in
           let m_h_list =
             List.map (match_handler expression env) m_h_list in
           Zelus.Ematch { is_size; is_total = false; e; handlers = m_h_list }
        | Epresent(p_h_list, eq_opt) ->
           let handlers =
             List.map (present_handler scondpat expression env) p_h_list in
           let default_opt =
             match eq_opt with
             | NoDefault -> Zelus.NoDefault
             | Init(e) -> Zelus.Init(expression env e)
             | Else(e) -> Zelus.Else(expression env e) in
           Zelus.Epresent({ handlers; default_opt }) 
        | Ereset(e_body, e_res) ->
           Zelus.Ereset(expression env e_body, expression env e_res)
        | Eassert(e_body) ->
           Zelus.Eassert
             { Zelus.a_body = expression env e_body;
               Zelus.a_hidden_env = Ident.Env.empty;
               Zelus.a_free_vars = Ident.S.empty }
        | Eforloop(f) ->
           Zelus.Eforloop(forloop_exp env f)
      in
      { Zelus.e_desc = desc; Zelus.e_loc = loc; Zelus.e_info = Info.no_info }
    
    and forloop_exp env 
          { for_size; for_kind; for_index; for_input; for_body; for_resume } =
      let for_size = Util.optional_map (expression env) for_size in
      let for_index, i_env =
        match for_index with
      | None -> None, Env.empty
      | Some(id) -> let m = fresh id in Some(m), Env.singleton id m in
      let for_input, i_env =
        trans_for_input env i_env for_input in
      let env = Env.append i_env env in
      let env_body, for_body = match for_body with
        | Forexp { exp; default } ->
           let exp = expression env exp in
           let default = Util.optional_map (expression env) default in
           env, Zelus.Forexp { exp = exp; default = default }
        | Forreturns { r_returns; r_block } ->
           let r_returns, env_v_list = for_vardec_list env r_returns in
           let env = Env.append env_v_list env in
           let env_block, r_block = block equation env_v_list env r_block in
           env_block,
           Zelus.Forreturns { r_returns; r_block; r_env = Ident.Env.empty } in
      let for_kind =
        match for_kind with
        | Kforeach -> Zelus.Kforeach
        | Kforward(e_opt) ->
           Zelus.Kforward(Util.optional_map (exit_expression env_body) e_opt) in
      { Zelus.for_size = for_size; Zelus.for_kind = for_kind;
        Zelus.for_index = for_index; Zelus.for_input = for_input; 
        Zelus.for_body = for_body;
        Zelus.for_resume = for_resume;
        Zelus.for_env = Ident.Env.empty }
    
    and exit_expression env { for_exit_kind; for_exit } =
      let k = match for_exit_kind with 
        | Ewhile -> Zelus.Ewhile
        | Euntil -> Zelus.Euntil | Eunless -> Zelus.Eunless in
      { Zelus.for_exit_kind = k; for_exit = expression env for_exit }
    
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
           else { Zelus.label = longname lname;
                  Zelus.arg = expression env e } ::
                  recordrec (S.add l labels) label_e_list in
      recordrec S.empty label_e_list
    
    and funexp env
           { desc = { f_vkind; f_kind; f_atomic; f_inline; f_args; f_body };
             loc } =
      let f_args, env = Util.mapfold arg env f_args in
      let f_body = result env f_body in
      { Zelus.f_vkind = vkind f_vkind;
        Zelus.f_kind = kind f_kind;
        Zelus.f_inline = f_inline; Zelus.f_atomic = f_atomic;
        Zelus.f_args = f_args; Zelus.f_body = f_body; Zelus.f_loc = loc;
        Zelus.f_env = Ident.Env.empty;
        Zelus.f_hidden_env = Ident.Env.empty }
    
    and arg env v_list =
      let v_list, env_v_list = vardec_list env v_list in
      v_list, Env.append env_v_list env
    
    and result env { desc; loc } =
      let r_desc =
        match desc with
        | Exp(e) -> Zelus.Exp(expression env e)
        | Returns(v_list, eq) ->
           let v_list, env_v_list = vardec_list env v_list in
           let env = Env.append env_v_list env in
           let eq = equation env_v_list env eq in
           Zelus.Returns(make_block loc v_list eq) in
      { r_desc; r_loc = loc; r_info = Info.no_info }
    
    (* type declarations. *)
    let rec type_decl { desc; loc } =
      let desc = match desc with
        | Eabstract_type -> Zelus.Eabstract_type
        | Eabbrev(ty) -> Zelus.Eabbrev(types Env.empty ty)
        | Evariant_type(constr_decl_list) ->
           Zelus.Evariant_type(List.map constr_decl constr_decl_list)
        | Erecord_type(n_ty_list) ->
           Zelus.Erecord_type
             (List.map (fun (n, ty) -> (n, types Env.empty ty)) n_ty_list) in
      { Zelus.desc = desc; Zelus.loc = loc }
    
    and constr_decl { desc; loc } =
      let desc = match desc with
        | Econstr0decl(n) -> Zelus.Econstr0decl(n)
        | Econstr1decl(n, ty_list) ->
           Zelus.Econstr1decl(n, List.map (types Env.empty) ty_list) in
      { Zelus.desc = desc; Zelus.loc = loc }
    
    let type_decls n_params_typdecl_list =
      List.map (fun (n, pars, typdecl) -> (n, pars, type_decl typdecl))
        n_params_typdecl_list
    
    let interface interf =
      try
        let desc = match interf.desc with
          | Einter_open(n) -> Zelus.Einter_open(n)
          | Einter_typedecl { name; ty_params; ty_decl } ->
             let ty_decl = type_decl ty_decl in
             Zelus.Einter_typedecl { name; ty_params; ty_decl }
          | Einter_constdecl { name; const; ty; info } ->
             let ty = types Env.empty ty in
             Zelus.Einter_constdecl { name; const = const; ty; info } in
        { Zelus.desc = desc; Zelus.loc = interf.loc }
      with
      | Error.Err(loc, err) -> Error.message loc err
    
    let implementation { desc; loc } =
      try
        let desc = match desc with
          | Eopen(n) -> Zelus.Eopen(n)
          | Eletdecl(d_leq) ->
             let d_leq, env = letin Env.empty d_leq in
             let d_names = Env.to_list env in
             Zelus.Eletdecl { d_names = d_names; d_leq = d_leq }
          | Etypedecl { name; ty_params; ty_decl } ->
             let ty_decl = type_decl ty_decl in
             Zelus.Etypedecl { name = name; ty_params; ty_decl } in
        { Zelus.desc = desc; Zelus.loc = loc }
      with
        Error.Err(loc, kind) -> Error.message loc kind
    
    (* translate a program. Invariant: all defined names in [i_list] *)
    (* have unique index names (pairwise distinct) and all less *)
    (* than [p_index] *)
    let program i_list = 
      let i_list = List.map implementation i_list in
      { Zelus.p_impl_list = i_list; Zelus.p_index = Ident.get () }
    
    let interface_list inter_list = Util.iter interface inter_list
    let implementation_list = program
  end
