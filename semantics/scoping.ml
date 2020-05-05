(* rewrite the parging tree into an ast *)
(* that is, change [id: String.t] into [id: Ident.t] *)

open Parsetree
open Ident
open Monad
open Opt

exception Error
        
module Error =
  struct
    type error =
      | Evar of string
      | Enon_linear_pat of string
      | Enon_linear_automaton of string
      | Eautomaton_with_mixed_transitions
                           
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
      raise Error 
end

module Env =
  struct
    include Map.Make(String)

    let append env0 env =
      fold (fun x v acc -> update x (function _ -> Some(v)) acc)
        env0 env
  end

module S = Set.Make (String)

(* compute the set of names defined by an equation *)
let rec buildeq defnames { desc } =
  match desc with
  | EQeq(pat, _) -> buildpat defnames pat
  | EQinit(n, _) -> if S.mem n defnames then defnames else S.add n defnames
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
  | EQmatch(_, m_h_list) ->
     List.fold_left build_match_handler defnames m_h_list
  | EQautomaton(a_h_list) ->
     let defnames_s_state, defnames =
       List.fold_left build_automaton_handler (S.empty, defnames) a_h_list in
     S.union defnames_s_state defnames
  | EQempty ->  defnames
                
and build_vardec defnames { desc = { var_name } } = S.add var_name defnames

and buildpat defnames { desc; loc } =
  List.fold_left
    (fun acc x ->
      if S.mem x acc then Error.error loc (Enon_linear_pat(x)); S.add x defnames)
    defnames desc

and build_match_handler defnames { desc = { m_pat; m_vars; m_body } } =
  let defnames_m_vars = List.fold_left build_vardec S.empty m_vars in
  let defnames_m_body = buildeq S.empty m_body in
  S.union defnames (S.diff defnames_m_body defnames_m_vars)

and build_state_name defnames { desc; loc } =
  match desc with
  | Estate0pat(n) | Estate1pat(n, _) ->
     if S.mem n defnames then Error.error loc (Error.Enon_linear_automaton(n));
     S.singleton(n)

and build_automaton_handler (defnames_s_state, defnames)
  { desc = { s_state; s_vars; s_body; s_until; s_unless } } =
  let defnames_s_state = build_state_name defnames_s_state s_state in
  let defnames_s_vars = List.fold_left build_vardec S.empty s_vars in
  let defnames_s_body = buildeq S.empty s_body in
  let defnames_s_trans =
    List.fold_left build_escape defnames_s_body s_until in
  let defnames_s_trans =
    List.fold_left build_escape defnames_s_trans s_unless in
  defnames_s_state,
  S.union defnames (S.diff defnames_s_trans defnames_s_vars)

and build_escape defnames { desc = { e_vars; e_body } } =
  let defnames_e_vars = List.fold_left build_vardec S.empty e_vars in
  let defnames_e_body = buildeq defnames e_body in
  S.union defnames (S.diff defnames_e_body defnames_e_vars)

let buildeq eq =
  let defnames = buildeq S.empty eq in
  S.fold (fun s acc -> let m = fresh s in Env.add s m acc) defnames Env.empty
  
let buildpat p =
  let defnames = buildpat S.empty p in
  S.fold (fun s acc -> let m = fresh s in Env.add s m acc) defnames Env.empty
               
let empty =
  let module S = Set.Make (Ident) in
  S.empty

let constant c =
  match c with
  | Eint(i) -> Ast.Eint(i)
  | Ebool(b) -> Ast.Ebool(b)
  | Efloat(f) -> Ast.Efloat(f)
  | Evoid -> Ast.Evoid
  | Estring(s) -> Ast.Estring(s)
  | Echar(c) -> Ast.Echar(c)
                
(* synchronous operators *)
let operator op =
  match op with
  | Efby -> Ast.Efby
  | Eifthenelse -> Ast.Eifthenelse
  | Eminusgreater -> Ast.Eminusgreater
  | Eunarypre -> Ast.Eunarypre

let lident ln =
  match ln with
  | Name(s) -> Lident.Name(s)
  | Modname { qual; id } -> Lident.Modname { Lident.qual = qual; Lident.id = id }

let pattern { desc; loc } =
  let desc = match desc with
    | Econstr0pat(f) -> Ast.Econstr0pat(lident f) in
    { Ast.desc = desc; Ast.loc = loc }, Env.empty

(* [env_pat] is the environment for names that appear on the *)
(* left of a definition. [env] is for names that appear on the right *)
let rec equation env_pat env { desc; loc } =
  let eq_desc =
    match desc with
    | EQeq(pat, e) ->
       let pat = pateq env_pat pat in
       let e = expression env e in
       Ast.EQeq(pat, e)
    | EQinit(x, e) ->
       let x =
         try Env.find x env_pat with | Not_found -> Error.error loc (Error.Evar(x)) in
       let e = expression env e in
       Ast.EQinit(x, e)
    | EQreset(eq, e) ->
       let eq = equation env_pat env eq in
       let e = expression env e in
       Ast.EQreset(eq, e)
    | EQand(and_eq_list) ->
       let and_eq_list = List.map (equation env_pat env) and_eq_list in
       Ast.EQand(and_eq_list)
    | EQlocal(v_list, eq) ->
       let v_list, env_v_list = Misc.mapfold (vardec env) Env.empty v_list in
       let env_pat = Env.append env_v_list env_pat in
       let env = Env.append env_v_list env in
       let eq = equation env_pat env eq in
       Ast.EQlocal(v_list, eq)
    | EQif(e, eq1, eq2) ->
       let e = expression env e in
       let eq1 = equation env_pat env eq1 in
       let eq2 = equation env_pat env eq2 in
       Ast.EQif(e, eq1, eq2)
    | EQmatch(e, m_h_list) ->
       let e = expression env e in
       let m_h_list = List.map (match_handler env_pat env) m_h_list in
       Ast.EQmatch(e, m_h_list)
    | EQautomaton(a_h_list) ->
       let is_weak, is_strong =
         List.fold_left
           (fun (is_weak, is_strong)
	        { desc = { s_until; s_unless } } ->
	     is_weak || (s_until <> []), is_strong || (s_unless <> []))
           (false, false) a_h_list in
       if is_weak && is_strong
       then Error.error loc (Error.Eautomaton_with_mixed_transitions)
       else
         let a_h_list =
           List.map (automaton_handler is_weak env_pat env) a_h_list in
         Ast.EQautomaton(is_weak, a_h_list)
    | EQempty ->
       Ast. EQempty in
  (* set the names defined in the equation *)
  { Ast.eq_desc = eq_desc; Ast.eq_write = empty; Ast.eq_loc = loc }

and vardec env acc { desc = { var_name; var_default }; loc } =
  if Env.mem var_name acc then Error.error loc (Enon_linear_pat(var_name));
  let var_default =
    match var_default with
    | Ewith_init(e) ->
       let e = expression env e in
       Ast.Ewith_init(e)
    | Ewith_default(e) ->
       let e = expression env e in
       Ast.Ewith_default(e)
    | Ewith_nothing -> Ast.Ewith_nothing in
  let m = Ident.fresh var_name in
  { Ast.var_name = m; Ast.var_default = var_default; Ast.var_loc = loc },
  Env.add var_name m acc

and state env { desc; loc } =
  let desc = match desc with
    | Estate0(f) ->
       let f = try Env.find f env with | Not_found -> Error.error loc (Error.Evar(f)) in
       Ast.Estate0(f)
  | Estate1(f, e_list) ->
     let f = try Env.find f env with | Not_found -> Error.error loc (Error.Evar(f)) in
     let e_list = List.map (expression env) e_list in
     Estate1(f, e_list) in
  { Ast.desc = desc; Ast.loc = loc }

and statepat acc { desc; loc } =
  let desc, acc = match desc with
    | Estate0pat(f) ->
       let fm = Ident.fresh f in
       Ast.Estate0pat(fm), Env.add f fm acc
    | Estate1pat(f, n_list) ->
       let fm = Ident.fresh f in
       let n_list, env =
         Misc.mapfold
           (fun acc n -> let m = Ident.fresh n in m, Env.add n m acc)
           acc n_list in
     Estate1pat(fm, n_list), Env.add f fm acc in
{ Ast.desc = desc; Ast.loc = loc }, acc

and pateq env_pat { desc; loc } =
  let desc =
    List.map
      (fun x ->
        try Env.find x env_pat with | Not_found -> Error.error loc (Error.Evar(x))) desc
  in { Ast.desc = desc; Ast.loc = loc }
   
and automaton_handler is_weak env_pat env
  { desc = { s_state; s_vars; s_body; s_until; s_unless }; loc } =
  let s_state, env_s_state = statepat Env.empty s_state in
  let env = Env.append env_s_state env in
  let s_vars, env_s_vars = Misc.mapfold (vardec env) Env.empty s_vars in
  let env_pat = Env.append env_s_vars env_pat in
  let env = Env.append env_s_vars env in
  let s_body = equation env_pat env s_body in
  let s_trans =
    List.map (escape env_pat env) (if is_weak then s_until else s_unless) in
  { Ast.s_state = s_state; Ast.s_vars = s_vars;
    Ast.s_body = s_body; Ast.s_trans = s_trans; Ast.s_loc = loc }

and escape env_pat env
  { desc = { e_reset; e_cond; e_vars; e_body; e_next_state }; loc } = 
  let e_cond, env_e_cond = scondpat env Env.empty e_cond in
  let env = Env.append env_e_cond env in
  let e_vars, env_e_vars = Misc.mapfold (vardec env) Env.empty e_vars in
  let env_pat = Env.append env_e_vars env_pat in
  let env = Env.append env_e_vars env in
  let e_body = equation env_pat env e_body in
  let e_next_state = state env e_next_state in
  { Ast.e_reset; Ast.e_cond = e_cond; Ast.e_vars = e_vars;
    Ast.e_body = e_body; Ast.e_next_state = e_next_state; Ast.e_loc = loc }

and scondpat env acc e_cond = expression env e_cond, acc
          
and match_handler env_pat env { desc = { m_pat; m_vars; m_body }; loc } = 
  let m_pat, env_m_pat = pattern m_pat in
  let env = Env.append env_m_pat env in
  let m_vars, env_m_vars = Misc.mapfold (vardec env) Env.empty m_vars in
  let env_pat = Env.append env_m_vars env_pat in
  let env = Env.append env_m_vars env in
  let m_body = equation env_pat env m_body in
  { Ast.m_pat = m_pat; Ast.m_vars = m_vars;
    Ast.m_body = m_body; Ast.m_loc = loc }

  
and expression env { desc; loc } =
  let desc =
    match desc with
    | Evar(Name(n)) ->
       begin try
           let m = Env.find n env in
           Ast.Elocal(m)
         with
         | Not_found -> Ast.Eglobal(Name(n))
       end
    | Evar(Modname _ as ln) -> Ast.Eglobal(lident ln)
    | Econst(c) -> Ast.Econst(constant c)
    | Econstr0(f) -> Ast.Econstr0(lident f)
    | Econstr1(f, e_list) -> Ast.Econstr1(lident f, List.map (expression env) e_list)
    | Elast(x) ->
       let x = try Env.find x env with | Not_found -> Error.error loc (Error.Evar(x)) in
       Ast.Elast(x)
    | Eop(op, e_list) ->
       let e_list = List.map (expression env) e_list in
       Ast.Eop(operator op, e_list)
    | Etuple(e_list) ->
       let e_list = List.map (expression env) e_list in
       Etuple(e_list)
    | Elet(is_rec, eq, e) ->
       let env_pat = buildeq eq in
       let env_let = Env.append env_pat env in
       let eq = equation env_pat (if is_rec then env_let else env) eq in
       let e = expression env_let e in
       Elet(is_rec, eq, e)
    | Eget(i, e) ->
       let e = expression env e in
       Eget(i, e)
    | Eapp(f, e_list) ->
       let e_list = List.map (expression env) e_list in
       Eapp(lident f, e_list) in
  { Ast.e_desc = desc; Ast.e_loc = loc }

let kind = function Efun -> Ast.Efun | Enode -> Ast.Enode

let funexp { desc = { f_kind; f_atomic; f_args; f_res; f_body }; loc } =
  let f_args, env_f_args = Misc.mapfold (vardec Env.empty) Env.empty f_args in
  let f_res, env_f = Misc.mapfold (vardec env_f_args) Env.empty f_res in
  let f_body = equation env_f (Env.append env_f env_f_args) f_body in
  { Ast.f_kind = kind f_kind; Ast.f_atomic = f_atomic;
    Ast.f_args = f_args; Ast.f_res = f_res;
    Ast.f_body = f_body; Ast.f_loc = loc }

let implementation { desc; loc } =
  let desc = match desc with
    | Eletdef(f, e) ->
       let e = expression Env.empty e in
       Ast.Eletdef(f, e)
    | Eletfun(f, fd) ->
       let fd = funexp fd in
       Ast.Eletfun(f, fd) in
  { Ast.desc = desc; Ast.loc = loc }

let program i_list = List.map implementation i_list
