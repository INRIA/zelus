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

(* free variables *)
(* this version expects that write variables be computed before *)

open Misc
open Ident
open Zelus

let rec fv_pat acc { pat_desc } =
  match pat_desc with
  | Ewildpat | Econstr0pat _ | Econstpat _ -> acc
  | Evarpat(x) -> 
     if S.mem x acc then acc else S.add x acc
  | Econstr1pat(_, pat_list) | Etuplepat(pat_list) ->
     List.fold_left fv_pat acc pat_list
  | Erecordpat(label_pat_list) ->
     List.fold_left
       (fun acc { arg } -> fv_pat acc arg) acc label_pat_list
  | Ealiaspat(p, name) ->
     let acc = if S.mem name acc then acc else S.add name acc in
     fv_pat acc p
  | Eorpat(p1, p2) -> fv_pat (fv_pat acc p1) p2
  | Etypeconstraintpat(p, _) -> fv_pat acc p
                              
let fv_statepat acc { desc } =
  match desc with
  | Estate0pat(id) ->
     if S.mem id acc then acc else S.add id acc
  | Estate1pat(id, id_list) ->
     let acc = if S.mem id acc then acc else S.add id acc in
     List.fold_left (fun acc id -> if S.mem id acc then acc else S.add id acc)
         acc id_list

let match_handlers fv_body bounded acc handlers =
  let match_handler acc ({ m_pat; m_body } as m) =
    let bounded = fv_pat bounded m_pat in
    let m_body, acc = fv_body bounded acc m_body in
    { m with m_body = m_body }, acc in
  Util.mapfold match_handler acc handlers

let present_handlers scondpat body bounded acc handlers =
  let present_handler acc ({ p_cond; p_body } as p) =
    let p_cond, bounded, acc = scondpat bounded acc p_cond in
    let p_body, acc = body bounded acc p_body in
    { p with p_cond; p_body = p_body }, acc in
  Util.mapfold present_handler acc handlers  

(* computes the set of (last and current) free variables from an expression *)
(* [bounded] is the set of bounded names in the current scope *)
let rec expression bounded ((last_acc, cur_acc) as acc) ({ e_desc } as e) =
  let e_desc, acc = match e_desc with
  | Eop(op, e_list) ->
     let e_list, acc = Util.mapfold (expression bounded) acc e_list in
     Eop(op, e_list), acc
  | Econst _ | Econstr0 _ | Eglobal _ ->
     e_desc, acc
  | Econstr1 { lname; arg_list } ->
     let arg_list, acc =
       Util.mapfold (expression bounded) acc arg_list in
     Econstr1 { lname; arg_list }, acc
  | Eapp(e, e_list) ->
     let e, acc = expression bounded acc e in
     let e_list, acc = Util.mapfold (expression bounded) acc e_list in
     Eapp(e, e_list), acc
  | Etuple(e_list) ->
     let e_list, acc = Util.mapfold (expression bounded) acc e_list in
     Etuple(e_list), acc
  | Elocal(n) ->
     let cur_acc =
       if (S.mem n cur_acc) || (S.mem n bounded)
       then cur_acc else S.add n cur_acc in
     e_desc, (last_acc, cur_acc)
  | Elast(n) ->
     let last_acc = if (S.mem n last_acc) || (S.mem n bounded) 
                    then last_acc else S.add n last_acc in
     e_desc, (last_acc, cur_acc)
  | Erecord_access(arg) ->
     let arg, acc = record bounded acc arg in
     Erecord_access(arg), acc
  | Etypeconstraint(e, ty) ->
     let e, acc = expression bounded acc e in
     Etypeconstraint(e, ty), acc
  | Erecord(f_e_list) ->
     let f_e_list, acc = Util.mapfold (record bounded) acc f_e_list in
     Erecord(f_e_list), acc
  | Erecord_with(e, f_e_list) ->
     let e, acc = expression bounded acc e in
     let f_e_list, acc = Util.mapfold (record bounded) acc f_e_list in
     Erecord_with(e, f_e_list), acc
  | Elet(l_eq, e) ->
     let local, (bounded, acc) = leq (bounded, acc) l_eq in
     let e, acc = expression bounded acc e in
     Elet(local, e), acc
  | Efun efun ->
     let efun, acc = funexp bounded acc efun in
     Efun efun, acc
  | Eassert e ->
     let e, acc = expression bounded acc e in Eassert(e), acc
  | Epresent { handlers; default_opt } ->
     let default_opt, acc =
       match default_opt with
       | NoDefault -> NoDefault, acc
       | Init(e) -> let e, acc = expression bounded acc e in Init(e), acc
       | Else(e) -> let e, acc = expression bounded acc e in Else(e), acc in
     let handlers, acc =
       present_handlers scondpat expression bounded acc handlers in
     Epresent { handlers; default_opt }, acc
  | Ematch({ e; handlers } as m) ->
     let e, acc = expression bounded acc e in
     let handlers, acc = match_handlers expression bounded acc handlers in
     Ematch({ m with e; handlers }), acc
  | Ereset(e, e_r) ->
     let e, acc = expression bounded acc e in
     let e_r, acc = expression bounded acc e_r in
     Ereset(e, e_r), acc
  | Eforloop({ for_size; for_kind; for_index; for_body } as f) ->
     let for_size, acc =
       Util.optional_with_map (expression bounded) acc for_size in
     let for_kind, acc =
       match for_kind with
       | Kforeach -> for_kind, acc
       | Kforward(e_opt) ->
          let e_opt, acc =
            Util.optional_with_map (expression bounded) acc e_opt in
          Kforward(e_opt), acc in
     let for_index, bounded, acc =
       defs_for_index bounded acc for_index in
     let for_body, acc = forloop_body_exp bounded acc for_body in
     Eforloop { f with for_size; for_kind; for_index; for_body }, acc in
  { e with e_desc }, acc

and record bounded acc { label; arg } =
  let arg, acc = expression bounded acc arg in { label; arg }, acc

and funexp bounded acc ({ f_args; f_body } as efun) =
  let f_args, (bounded, acc) = args (bounded, acc) f_args in
  let f_body, acc = result bounded acc f_body in
  { efun with f_args; f_body }, acc
  
and args (bounded, acc) arg_list =
  Util.mapfold vardec_list (bounded, acc) arg_list

and vardec_list (bounded, acc) vardec_list =
  (* first compute the set of bounded names *)
  let bounded =
    List.fold_left
      (fun bounded { var_name } -> S.add var_name bounded) bounded vardec_list in
  (* then the list of visible names *)
  let vardec_list, acc = Util.mapfold (vardec bounded) acc vardec_list in
  vardec_list, (bounded, acc)
  
and vardec bounded acc ({ var_default; var_init } as vardec) =
  let var_default, acc =
    Util.optional_with_map
      (fun acc e -> expression bounded acc e) acc var_default in
  let var_init, acc =
    Util.optional_with_map
      (fun acc e -> expression bounded acc e) acc var_init in
  { vardec with var_default; var_init }, acc
  
and result bounded acc ({ r_desc } as result) =
  let r_desc, acc = match r_desc with
    | Exp(e) -> let e, acc = expression bounded acc e in Exp(e), acc
    | Returns(b) ->
       let b, bounded, acc = block bounded acc b in
       Returns(b), acc in
  { result with r_desc }, acc

and equation bounded acc ({ eq_desc } as eq) =
  let eq_desc, acc = match eq_desc with
    | EQeq(p, e) ->
       let e, acc = expression bounded acc e in
       EQeq(p, e), acc
    | EQinit(id, e) ->
       let e, acc = expression bounded acc e in
       EQinit(id, e), acc
    | EQemit(id, e_opt) ->
       let e_opt, acc = Util.optional_with_map (expression bounded) acc e_opt in
       EQemit(id, e_opt), acc
    | EQif(e, eq1, eq2) ->
       let e, acc = expression bounded acc e in
       let eq1, acc = equation bounded acc eq1 in
       let eq2, acc = equation bounded acc eq2 in
       EQif(e, eq1, eq2), acc
    | EQmatch({ e; handlers } as m) ->
       let e, acc = expression bounded acc e in
       let handlers, acc = match_handlers equation bounded acc handlers in
       EQmatch({ m with e; handlers }), acc
    | EQautomaton({ handlers; state_opt } as a_h) ->
       let state_opt, acc =
         Util.optional_with_map (state bounded) acc state_opt in
       let handlers, acc = automaton_handlers bounded acc handlers in
       EQautomaton({ a_h with handlers; state_opt }), acc
    | EQpresent({ handlers; default_opt }) ->
       let default_opt, acc =
         match default_opt with
         | NoDefault -> NoDefault, acc
         | Init(eq) -> let eq, acc = equation bounded acc eq in Init(eq), acc
         | Else(eq) -> let eq, acc = equation bounded acc eq in Else(eq), acc in
       let handlers, acc =
         present_handlers scondpat equation bounded acc handlers in
       EQpresent({ handlers; default_opt }), acc
    | EQempty -> EQempty, acc
    | EQreset(eq, e) ->
     let e, acc = expression bounded acc e in
     let eq, acc = equation bounded acc eq in
     EQreset(eq, e), acc
  | EQder(id, e, e_opt, handlers) ->
     let e, acc = expression bounded acc e in
     let e_opt, acc = Util.optional_with_map (expression bounded) acc e_opt in
     let handlers, acc =
       present_handlers scondpat expression bounded acc handlers in
       EQder(id, e, e_opt, handlers), acc 
  | EQlocal(b) ->
     let b, bounded, acc = block bounded acc b in
     EQlocal(b), acc
  | EQand(eq_list) ->
     let eq_list, acc = Util.mapfold (equation bounded) acc eq_list in
     EQand(eq_list), acc
  | EQlet(l_eq, eq) ->
     let l_eq, (bounded, acc) = leq (bounded, acc) l_eq in
     let eq, acc = equation bounded acc eq in
     EQlet(l_eq, eq), acc
  | EQassert(e) ->
     let e, acc = expression bounded acc e in
     EQassert(e), acc
  | EQforloop({ for_size; for_kind; for_index; for_body } as f) ->
      let for_size, acc =
        Util.optional_with_map (expression bounded) acc for_size in
      let for_kind, acc =
        match for_kind with
        | Kforeach -> for_kind, acc
        | Kforward(e_opt) ->
           let e_opt, acc =
             Util.optional_with_map (expression bounded) acc e_opt in
           Kforward(e_opt), acc in
      let for_index, bounded, acc =
        defs_for_index bounded acc for_index in
      let for_body, acc = forloop_body_eq bounded acc for_body in
      EQforloop({ f with for_size; for_kind; for_index; for_body }), acc in
  { eq with eq_desc }, acc

and state bounded acc ({ desc } as se) =
  let desc, acc = match desc with
    | Estate0 _ -> desc, acc
    | Estate1(f, e_list) ->
       let e_list, acc = Util.mapfold (expression bounded) acc e_list in
       Estate1(f, e_list), acc
    | Estateif(e, se1, se2) ->
       let e, acc = expression bounded acc e in
       let se1, acc = state bounded acc se1 in
       let se2, acc = state bounded acc se2 in
       Estateif(e, se1, se2), acc in
  { se with desc }, acc

and automaton_handlers bounded acc handlers =
  let automaton_handler acc ({ s_state; s_let; s_body; s_trans } as h) =
    let bounded = fv_statepat bounded s_state in
    let s_let, bounded, acc = lets bounded acc s_let in
    let s_body, bounded, acc = block bounded acc s_body in
    let s_trans, acc =
      Util.mapfold (escape bounded) acc s_trans in
    { h with s_let; s_body; s_trans },
    acc in
  Util.mapfold automaton_handler acc handlers
   
and escape bounded acc ({ e_cond; e_let; e_body; e_next_state } as esc) =
  let e_cond, bounded, acc = scondpat bounded acc e_cond in
  let e_let, bounded, acc = lets bounded acc e_let in
  let e_body, bounded, acc = block bounded acc e_body in
  let e_next_state, acc = state bounded acc e_next_state in
  { esc with e_cond = e_cond; e_let; e_body = e_body;
             e_next_state = e_next_state },
  acc
  
and scondpat bounded acc ({ desc } as scpat) =
  let desc, bounded, acc = match desc with
    | Econdand(scpat1, scpat2) ->
       let scpat1, bounded, acc = scondpat bounded acc scpat1 in
       let scpat2, bounded, acc = scondpat bounded acc scpat2 in
       Econdand(scpat1, scpat2), bounded, acc
    | Econdor(scpat1, scpat2) ->
       let scpat1, bounded, acc = scondpat bounded acc scpat1 in
       let scpat2, bounded, acc = scondpat bounded acc scpat2 in
       Econdor(scpat1, scpat2), bounded, acc
    | Econdexp(e) ->
       let e, acc = expression bounded acc e in
       Econdexp(e), bounded, acc
    | Econdpat(e, p) ->
       let e, acc = expression bounded acc e in
       Econdpat(e, p), fv_pat bounded p, acc
    | Econdon(scpat, e) ->
       let e, acc = expression bounded acc e in
       let scpat, bounded, acc = scondpat bounded acc scpat in
       Econdon(scpat, e), bounded, acc in
  { scpat with desc = desc }, bounded, acc

(* Sequence [let eq1 in let eq2 in ... let eqn in ...] *)
and leq (bounded, acc) ({ l_rec; l_eq } as leq) =
  (* warning; the computation of write variables must be done before *)
  let bounded_with_locals =
    S.union (Deftypes.names bounded l_eq.eq_write) bounded in
  let l_eq, acc =
    equation (if l_rec then bounded_with_locals else bounded) acc l_eq in
  { leq with l_eq }, (bounded_with_locals, acc)

and lets bounded acc l =
  let l, (bounded, acc) = Util.mapfold leq (bounded, acc) l in
  l, bounded, acc
  
and block bounded acc ({ b_vars; b_body } as b) =
  let b_vars, (bounded, acc) = vardec_list (bounded, acc) b_vars in
  let b_body, acc = equation bounded acc b_body in
  { b with b_vars; b_body }, bounded, acc

and forloop_body_eq bounded acc ({ for_block; for_out } as for_eq) =
  let for_out_one (bounded, acc)
        ({ desc = { for_name; for_init; for_default; for_out_name } } as fo) =
    let for_init, acc =
      Util.optional_with_map (expression bounded) acc for_init in
    let for_default, acc =
      Util.optional_with_map (expression bounded) acc for_default in
    { fo with desc = { for_name; for_init; for_default; for_out_name } },
    (S.add for_name bounded, acc) in 
  let for_out, (bounded, acc) =
    Util.mapfold for_out_one (bounded, acc) for_out in
  let for_block, defnames, dv_for_block = block bounded acc for_block in
  { for_eq with for_out; for_block }, acc

and forloop_body_exp bounded acc for_body =
  match for_body with
  | Forexp { exp; default } ->
     let exp, acc = expression bounded acc exp in
     let default, acc =
       Util.optional_with_map (expression bounded) acc default in
     Forexp { exp; default }, acc
  | Forreturns({ returns; body } as f_returns) ->
     let returns, (bounded, acc) =
       for_vardec_list (bounded, acc) returns in
     let body, _, acc = block bounded acc body in
     Forreturns({ f_returns with returns; body }), acc

and for_vardec_list (bounded, acc) for_vardec_list =
  (* first compute the set of bounded names *)
  let bounded =
    List.fold_left
      (fun bounded { desc = { for_vardec = { var_name } } } ->
        S.add var_name bounded) bounded for_vardec_list in
  (* then the list of visible names *)
  let for_vardec_list, acc =
    Util.mapfold (for_vardec bounded) acc for_vardec_list in
  for_vardec_list, (bounded, acc)

and for_vardec bounded acc ({ desc = ({ for_vardec } as v) } as fv) =
  let for_vardec, acc = vardec bounded acc for_vardec in
  { fv with desc = { v with for_vardec } }, acc

and defs_for_index bounded acc for_index = 
  let index (bounded, acc) ({ desc } as i) =
    let desc, bounded, acc = match desc with
      | Einput { id; e; by } ->
         let e, acc = expression bounded acc e in
         let by, acc = Util.optional_with_map (expression bounded) acc by in
         Einput { id; e; by }, bounded, acc         
      | Eindex { id; e_left; e_right; dir } ->
         let e_left, acc = expression bounded acc e_left in
         let e_right, acc = expression bounded acc e_right in
         Eindex { id; e_left; e_right; dir }, bounded, acc in
    { i with desc }, (bounded, acc) in
  let for_index, (bounded, acc) =
    Util.mapfold index (bounded, acc) for_index in
  for_index, bounded, acc
