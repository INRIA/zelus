(* compute write variables for every equation and block *)

open Ident
open Ast
open Monad
   
let fv_pateq acc { desc = desc } =
  List.fold_left (fun acc x -> S.add x acc) acc desc
  
let rec equation ({ eq_desc } as eq)=
  let eq_desc, def =
    match eq_desc with
    | EQeq(pat, e) ->
       EQeq(pat, expression e), fv_pateq S.empty pat
    | EQinit(n, e) ->
       EQinit(n, expression e), S.singleton n
    | EQreset(eq, e) ->
       let eq, def = equation eq in
       EQreset(eq, expression e), def
    | EQand(and_eq_list) ->
       let and_eq_list, def =
         Misc.mapfold
           (fun acc eq ->
             let eq, def = equation eq in eq, S.union def acc)
           S.empty and_eq_list in
       EQand(and_eq_list), def
    | EQlocal(v_list, eq) ->
       let v_list, def = Misc.mapfold vardec S.empty v_list in
       let eq, def_eq = equation eq in
       EQlocal(v_list, eq), S.diff def_eq def
    | EQif(e, eq1, eq2) ->
       let e = expression e in
       let eq1, def1 = equation eq1 in
       let eq2, def2 = equation eq2 in
       let def = S.union def1 def2 in
       EQif(e, eq1, eq2), def
    | EQmatch(e, m_h_list) ->
       let m_h_list, def = Misc.mapfold match_handler S.empty m_h_list in
       EQmatch(expression e, m_h_list), def
    | EQautomaton(is_weak, a_h_list) ->
       let a_h_list, def =
         Misc.mapfold automaton_handler S.empty a_h_list in
       EQautomaton(is_weak, a_h_list), def
    | EQempty -> EQempty, S.empty in
  (* set the names defined in the equation *)
  { eq with eq_desc = eq_desc; eq_write = def }, def

and vardec acc ({ var_name; var_default } as v) =
  let var_default =
    match var_default with
    | Ewith_init(e) -> Ewith_init(expression e)
    | Ewith_default(e) -> Ewith_default(expression e)
    | Ewith_nothing -> Ewith_nothing
    | Ewith_last -> Ewith_last in
  { v with var_default = var_default }, S.add var_name acc

and state ({ desc } as st) =
  match desc with
  | Estate0 _ -> st
  | Estate1(f, e_list) ->
     { st with desc = Estate1(f, List.map expression e_list) }

and automaton_handler acc ({ s_vars; s_body; s_trans } as h) =
  let s_vars, def_vars = Misc.mapfold vardec S.empty s_vars in
  let s_body, def_body = equation s_body in
  let s_trans, def_trans = Misc.mapfold escape S.empty s_trans in
  { h with s_vars = s_vars; s_body = s_body; s_trans = s_trans },
  S.union (S.diff (S.union def_body def_trans) def_vars) acc

and escape acc ({ e_reset; e_cond; e_vars; e_body; e_next_state } as esc) =
  let e_cond = scondpat e_cond in
  let e_vars, def_vars = Misc.mapfold vardec S.empty e_vars in
  let e_body, def_body = equation e_body in
  let e_next_state = state e_next_state in
  { esc with e_reset; e_cond = e_cond; e_vars = e_vars;
    e_body = e_body; e_next_state = e_next_state },
  S.union (S.diff def_body def_vars) acc
  
and scondpat e_cond = expression e_cond
          
and match_handler acc ({ m_vars; m_body } as m) =
  let m_vars, def_vars = Misc.mapfold vardec S.empty m_vars in
  let m_body, def_body = equation m_body in
  { m with m_vars = m_vars; m_body = m_body },
  S.union (S.diff def_body def_vars) acc

and expression ({ e_desc = desc } as e) =
  let desc =
    match desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> desc
    | Econstr1(f, e_list) ->
       Econstr1(f, List.map expression e_list)
    | Eop(op, e_list) ->
       Eop(op, List.map expression e_list)
    | Etuple(e_list) -> Etuple(List.map expression e_list)
    | Elet(is_rec, eq, e) ->
       let eq, _ = equation eq in
       Elet(is_rec, eq, expression e)
    | Eget(i, e) -> Eget(i, expression e)
    | Eapp(f, e_list) ->
       Eapp(f, List.map expression e_list) in
  { e with e_desc = desc }

let funexp ({ f_args; f_res; f_body } as fd) =
  let f_args, _ = Misc.mapfold vardec S.empty f_args in
  let f_res, _ = Misc.mapfold vardec S.empty f_res in
  let f_body, _ = equation f_body in
  { fd with f_args = f_args; f_res = f_res; f_body = f_body }

let implementation ({ desc } as i) =
  let desc = match desc with
    | Eletdef(f, e) -> Eletdef(f, expression e)
    | Eletfun(f, fd) -> Eletfun(f, funexp fd) in
  { i with desc = desc }
  
let program i_list = List.map implementation i_list
