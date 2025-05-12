(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)


(* compute write variables for every equation and block *)

module type INFO =
  sig type ienv val no_ienv : ienv end

module Make (Info: INFO) =
  struct
    open Ident
    open Zelus
    open Defnames
    
    (* build an environment *)
    let build id env = Env.add id Info.no_ienv env
    
    let build_from_defnames { dv; di; der } = 
      S.fold build dv (S.fold build di (S.fold build der Env.empty))
    
    let build_from_names n_set = S.fold build n_set Env.empty
    
    let rec fv_pat acc { pat_desc } =
      match pat_desc with
      | Ewildpat | Econstr0pat _ | Econstpat _ -> acc
      | Evarpat(x) ->
         if S.mem x acc then acc else S.add x acc
      | Econstr1pat(_, pat_list) | Etuplepat(pat_list) | Earraypat(pat_list) ->
         List.fold_left fv_pat acc pat_list
      | Erecordpat(label_pat_list) ->
         List.fold_left
           (fun acc { arg } -> fv_pat acc arg) acc label_pat_list
      | Ealiaspat(p, name) ->
         let acc =
           if S.mem name acc
           then acc else S.add name acc in
         fv_pat acc p
      | Eorpat(p1, _) -> fv_pat acc p1
      | Etypeconstraintpat(p, _) -> fv_pat acc p

    (* names defined by an equation *)
    let defnames eq =
      (* computes the set of names that appear on the left of an "=" *)
      let rec equation bounded acc { eq_desc } = match eq_desc with
        | EQeq(p, _) -> fv_pat acc p
        | EQsizefun { sf_id = n } | EQder { id = n }
          | EQinit(n, _) | EQemit(n, _) ->
           if S.mem n bounded then acc else S.add n acc
        | EQif { eq_true; eq_false } ->
           equation bounded (equation bounded acc eq_true) eq_false
        | EQand { eq_list } -> List.fold_left (equation bounded) acc eq_list
        | EQlocal(b) -> let _, acc = block bounded acc b in acc
        | EQlet(l_eq, eq) ->
           let bounded = leq bounded acc l_eq in equation bounded acc eq
        | EQreset(eq, _) -> equation bounded acc eq
        | EQautomaton { handlers } ->
           let trans bounded acc { e_body } =
             let _, acc = block bounded acc e_body in acc in
           let handler bounded acc { s_body; s_trans } =
             let bounded, acc = block bounded acc s_body in
             List.fold_left (trans bounded) acc s_trans in
           List.fold_left (handler bounded) acc handlers
        | EQpresent { handlers; default_opt } ->
           let handler bounded acc { p_body } = equation bounded acc p_body in
           let acc = List.fold_left (handler bounded) acc handlers in
           let acc = match default_opt with
             | NoDefault -> acc | Init(eq) | Else(eq) ->
                                   equation bounded acc eq in
           acc
        | EQmatch { handlers } ->
           let handler acc { m_pat; m_body } =
             equation (fv_pat bounded m_pat) acc m_body in
           List.fold_left handler acc handlers
        | EQempty | EQassert _ -> acc
        | EQforloop { for_body = { for_out } } ->
           let for_out_one bounded acc { desc = { for_name } } =
             if S.mem for_name bounded then acc else S.add for_name acc in
           List.fold_left (for_out_one bounded) acc for_out
        and block bounded acc { b_vars; b_body } =
          let bounded =
            List.fold_left (fun bounded { var_name } -> S.add var_name bounded)
              bounded b_vars in
          bounded, equation bounded acc b_body
        and leq bounded acc { l_eq } = equation bounded acc l_eq in
      equation S.empty S.empty eq
    
    (* computes [dv] and [di] *)
    let rec equation ({ eq_desc } as eq)=
      let eq_desc, def =
        match eq_desc with
        | EQeq(pat, e) ->
           EQeq(pat, expression e),
           { Defnames.empty with dv = fv_pat S.empty pat }
        | EQsizefun ({ sf_id; sf_id_list; sf_e } as sf) ->
           let dv = 
             List.fold_left (fun acc id -> S.add id acc) S.empty sf_id_list in
           let sf_e = expression sf_e in
           let sf_env = build_from_names dv in
           EQsizefun { sf with sf_id; sf_id_list; sf_e; sf_env },
           { Defnames.empty with dv = S.singleton sf_id }
        | EQder { id; e; e_opt; handlers } ->
           let e_opt, di =
             match e_opt with
             | None -> None, S.empty
             | Some(e) -> Some(expression e), S.singleton id in
           let handlers =
             List.map
               (fun ({ p_body } as p) -> { p with p_body = expression p_body })
               handlers in
           let e = expression e in
           EQder { id; e; e_opt; handlers },
           { Defnames.empty with der = S.singleton id; di }
        | EQinit(x, e) ->
           EQinit(x, expression e),
           { Defnames.empty with di = S.singleton x }
        | EQemit(x, e_opt) ->
           EQemit(x, Util.optional_map expression e_opt),
           { Defnames.empty with dv = S.singleton x }
        | EQreset(eq, e) ->
           let eq, def = equation eq in
           EQreset(eq, expression e), def
        | EQand({ eq_list } as a) ->
           let eq_list, def =
             Util.mapfold
               (fun acc eq ->
                 let eq, def = equation eq in eq, Defnames.union def acc)
               Defnames.empty eq_list in
           EQand { a with eq_list }, def
        | EQlocal(b_eq) ->
           let b_eq, def_eq, _ = block b_eq in
           EQlocal(b_eq), def_eq
        | EQlet(l, eq) ->
           let l = leq l in
           let eq, def = equation eq in
           EQlet(l, eq), def
        | EQif { e; eq_true; eq_false } ->
           let e = expression e in
           let eq_true, def_true = equation eq_true in
           let eq_false, def_false = equation eq_false in
           let def = Defnames.union def_true def_false in
           EQif { e; eq_true; eq_false }, def
        | EQmatch({ e; handlers } as m) ->
           let match_handler acc ({ m_pat; m_body } as m) =
             let m_body, def_body = equation m_body in
             let fv = fv_pat S.empty m_pat in
             let m_env = build_from_names fv in
             { m with m_body = m_body; m_env }, Defnames.union acc def_body in
           let e = expression e in
           let handlers, def =
             Util.mapfold match_handler Defnames.empty handlers in
           EQmatch({ m with e; handlers }), def
        | EQautomaton({ handlers; state_opt } as a_h) ->
           let state_opt =
             Util.optional_map state state_opt in
           let handlers, def =
             Util.mapfold automaton_handler empty handlers in
           EQautomaton({ a_h with handlers; state_opt }), def
        | EQpresent({ handlers; default_opt }) ->
           let present_handler acc ({ p_cond; p_body } as p) =
             let p_body, def_body = equation p_body in
             let p_cond, dv_cond = scondpat S.empty p_cond in
             let p_env = build_from_names dv_cond in
             { p with p_body = p_body; p_env }, Defnames.union acc def_body in
           let handlers, def =
             Util.mapfold present_handler Defnames.empty handlers in
           let default_opt, def_opt =
             match default_opt with
             | NoDefault -> NoDefault, Defnames.empty
             | Init(eq) -> let eq, def = equation eq in Init(eq), def
             | Else(eq) -> let eq, def = equation eq in Else(eq), def in
           EQpresent({ handlers; default_opt }), Defnames.union def def_opt
        | EQempty -> EQempty, Defnames.empty
        | EQassert(e) -> EQassert(expression e), Defnames.empty
        | EQforloop({ for_size; for_kind; for_index;
                      for_input; for_body = { for_out; for_block } } as f) ->
           let for_size = Util.optional_map expression for_size in
           let for_kind =
             match for_kind with
             | Kforeach -> for_kind
             | Kforward(e_opt) ->
                Kforward(Util.optional_map exit_expression e_opt) in
           let dv_index = 
             Util.optional (fun acc x -> S.add x acc) S.empty for_index in
           let for_input, dv_input =
             for_input_w dv_index for_input in
           (* From outside, when the output is [xi out x] *)
           (* the defined variable in the loop body is [x], not [xi] *)
           let for_out_one (acc, h_out)
                 ({ desc = 
                      ({ for_name; for_init; for_default; for_out_name } as v)}
                  as fo) =
             let acc, h_out =
               match for_out_name with
               | None -> acc, h_out
               | Some(x) ->
                  S.add for_name acc, Env.add for_name x h_out in
             let for_init = Util.optional_map expression for_init in
             let for_default = Util.optional_map expression for_default in
             { fo with desc = 
                         { v with for_name; for_init; for_default; 
                                  for_out_name } },
             (acc, h_out) in
           let for_out, (dv_out, h_out) =
             Util.mapfold for_out_one (S.empty, Env.empty) for_out in
           let for_block, defnames, dv_for_block = block for_block in
           let defnames = Defnames.subst defnames h_out in
           let for_env = build_from_names dv_input in
           let for_out_env = build_from_names dv_out in
           EQforloop({ f with for_size; for_kind; for_input; for_env;
                              for_body = { for_out; for_block; for_out_env; }}),
           defnames in
      (* set the names defined in the equation *)
      { eq with eq_desc = eq_desc; eq_write = def }, def
    
    (* Sequence [let eq1 in let eq2 in ... let eqn in ...] *)
    and lets l = List.map leq l
    
    and leq ({ l_eq } as l) =
      let l_eq, def = equation l_eq in 
      let l_env = build_from_defnames def in
      { l with l_eq; l_env }
    
    (* [returns a new block whose body is an equation [eq];
     *- [def] the defined variables in [eq] that are not local;
     *- [dv_b] the defined local variables *)
    and block ({ b_vars; b_body } as b) =
      let b_body, def_body = equation b_body in
      let b_vars, dv_b = Util.mapfold (vardec def_body) S.empty b_vars in
      let def = Defnames.diff def_body dv_b in
      let b_env = build_from_names dv_b in
      { b with b_vars; b_body; b_write = def; b_env }, def, dv_b
    
    (* [di] are the names for which an equation [init x = ...] *)
    (* appears in the body *)
    and vardec { di } acc ({ var_name; var_default; var_init } as v) =
      { v with var_default = Util.optional_map expression var_default;
               var_init = Util.optional_map expression var_init;
               var_init_in_eq = S.mem var_name di },
      S.add var_name acc
    
    and state ({ desc } as se) =
      match desc with
      | Estate0 _ -> se
      | Estate1(f, e_list) ->
         { se with desc = Estate1(f, List.map expression e_list) }
      | Estateif(e, se1, se2) ->
         { se with desc = Estateif(expression e, state se1, state se2) }
    
    and automaton_handler acc ({ s_state; s_let; s_body; s_trans } as h) =
      let dv_state = fv_statepat s_state in
      let s_let = lets s_let in
      let s_body, def_eq, dv_b = block s_body in
      let s_trans, def_escape = Util.mapfold escape Defnames.empty s_trans in
      let s_env = build_from_names dv_state in
      { h with s_let; s_body; s_trans; s_env },
      Defnames.union (Defnames.union def_eq (Defnames.diff def_escape dv_b)) acc
    
    and escape acc ({ e_cond; e_let; e_body; e_next_state } as esc) =
      let e_cond, dv_cond = scondpat S.empty e_cond in
      let e_let = lets e_let in
      let e_body, def_eq, _ = block e_body in
      let e_next_state = state e_next_state in
      let e_env = build_from_names dv_cond in
      { esc with e_cond = e_cond; e_let; e_body = e_body;
                 e_next_state = e_next_state; e_env },
      Defnames.union def_eq acc
    
    and scondpat acc ({ desc } as scpat) =
      let desc, acc = match desc with
        | Econdand(scpat1, scpat2) ->
           let scpat1, acc = scondpat acc scpat1 in
           let scpat2, acc = scondpat acc scpat2 in
           Econdand(scpat1, scpat2), acc
        | Econdor(scpat1, scpat2) ->
           let scpat1, acc = scondpat acc scpat1 in
           let scpat2, acc = scondpat acc scpat2 in
           Econdor(scpat1, scpat2), acc
        | Econdexp(e) ->
           Econdexp(expression e), acc
        | Econdpat(e, p) ->
           let acc = fv_pat acc p in
           Econdpat(expression e, p), acc
        | Econdon(scpat, e) ->
           let scpat, acc = scondpat acc scpat in
           Econdon(scpat, expression e), acc in
      { scpat with desc = desc }, acc
    
    and fv_statepat { desc } =
      match desc with
      | Estate0pat(id) -> S.singleton id
      | Estate1pat(id, id_list) -> 
         List.fold_left (fun acc id -> S.add id acc) (S.singleton id) id_list
    
    and expression ({ e_desc } as e) =
      let desc =
        match e_desc with
        | Evar _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e_desc
        | Econstr1 { lname; arg_list } ->
           Econstr1 {lname; arg_list = List.map expression arg_list }
        | Eop(op, e_list) ->
           Eop(op, List.map expression e_list)
        | Etuple(e_list) -> Etuple(List.map expression e_list)
        | Elet(l_eq, e) -> Elet(leq l_eq, expression e)
        | Elocal(b_eq, e) -> 
           let b_eq, _, _ = block b_eq in
           Elocal(b_eq, expression e)
        | Eapp { is_inline; f; arg_list } ->
           Eapp { is_inline; f = expression f; 
                  arg_list = List.map expression arg_list }
        | Esizeapp({ f } as app) -> Esizeapp({ app with f = expression f})
        | Erecord_access({ label; arg }) ->
           Erecord_access({ label; arg = expression arg })
        | Erecord(le_list) ->
           let le_list =
             List.map (fun {label; arg} -> {label; arg = expression arg}) le_list in
           Erecord(le_list)
        | Erecord_with(e, le_list) ->
           let e = expression e in
           let le_list =
             List.map (fun {label; arg} -> {label; arg = expression arg}) le_list in
           Erecord_with(e, le_list)
        | Etypeconstraint(e, ty) ->
           Etypeconstraint(expression e, ty)
        | Efun(fd) -> Efun(funexp fd)
        | Ematch({ e; handlers } as m) ->
           let e = expression e in
           let handlers =
             List.map
               (fun ({ m_body } as m) -> { m with m_body = expression m_body })
               handlers in
           Ematch({ m with e; handlers })
        | Epresent({ handlers; default_opt }) ->
           let handlers =
             List.map
               (fun ({ p_body } as p) -> { p with p_body = expression p_body })
               handlers in
           let default_opt =
             match default_opt with
             | NoDefault -> NoDefault
             | Init(e) -> Init(expression e)
             | Else(e) -> Else(expression e) in
           Epresent({ handlers; default_opt })
        | Ereset(e_body, e_res) ->
           Ereset(expression e_body, expression e_res)
        | Eassert(e_body) -> Eassert(expression e_body)
        | Eforloop({ for_size; for_index; for_kind; for_input; for_body } as f) ->
           let for_size = Util.optional_map expression for_size in
           let for_kind =
             match for_kind with
             | Kforeach -> for_kind
             | Kforward(e_opt) ->
                Kforward(Util.optional_map exit_expression e_opt) in
           let dv_index = 
             Util.optional (fun acc x -> S.add x acc) S.empty for_index in
           let for_input, dv_input =
             for_input_w dv_index for_input in
           let for_body =
             match for_body with
             | Forexp { exp; default } ->
                Forexp { exp = expression exp;
                         default = Util.optional_map expression default }
             | Forreturns { r_returns; r_block } ->
                let r_block, _, _ = block r_block in
                let r_returns, dv = Util.mapfold for_vardec S.empty r_returns in
                let r_env = build_from_names dv in
                Forreturns({ r_returns; r_block; r_env }) in
           let for_env = build_from_names dv_input in
           Eforloop
             ({ f with for_size; for_kind; for_input; for_env; for_body }) in
      { e with e_desc = desc }
    
    and for_vardec acc ({ desc = ({ for_vardec } as v) } as fv) =
      let for_vardec, acc = vardec Defnames.empty acc for_vardec in
      { fv with desc = { v with for_vardec } }, acc
    
    and for_input_w acc for_input_list =
      let input acc ({ desc } as i) =
        let desc, acc = match desc with
          | Einput { id; e; by } ->
             let by = Util.optional_map expression by in
             Einput { id; e = expression e; by }, S.add id acc
          | Eindex { id; e_left; e_right; dir } ->
             Eindex { id; e_left = expression e_left;
                      e_right = expression e_right; dir }, S.add id acc in
        { i with desc }, acc in
      Util.mapfold input acc for_input_list
    
    and exit_expression ({ for_exit } as e) =
      { e with for_exit = expression for_exit }
    
    and arg acc v_list = Util.mapfold (vardec Defnames.empty) acc v_list
    
    and funexp ({ f_args; f_body } as fd) =
      let f_args, dv_args = Util.mapfold arg S.empty f_args in
      let f_body = result f_body in
      let f_env = build_from_names dv_args in
      { fd with f_args = f_args; f_body = f_body; f_env }
    
    and result ({ r_desc } as r) =
      let r_desc =
        match r_desc with
        | Exp(e) -> Exp(expression e)
        | Returns(b_eq) ->
           let b_eq, _, _ = block b_eq in
           Returns(b_eq) in
      { r with r_desc }
    
    let implementation ({ desc } as i) =
      let desc = match desc with
        | Eopen _ -> desc
        | Eletdecl({ d_leq } as d) ->
           Eletdecl { d with d_leq = leq d_leq }
        | Etypedecl _ -> desc in
      { i with desc }
    
    let program ({ p_impl_list } as p) = 
      { p with p_impl_list = List.map implementation p_impl_list }
  end
