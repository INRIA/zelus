(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* initialization check *)

(* we do very simple check, following STTT'04, with a simple extension *)
(* for constraining the left limit (last x) in continuous systems.
 *- E.g., [init x = e] and [pre(e)] are
 *- valid if [e] is initialized.
 *- when x is declared with [init x = e], then last x is
 *- marked to be initialized with type 0.
 *- if x is not explicitly initialized, it gets type 1 *)
open Misc
open Ident
open Global
open Zelus
open Location
open Deftypes
open Definit
open Init

let print x = Misc.internal_error "unbound" Printer.name x

(* Main error message *)
type error =
  | Iless_than of ti * ti (* not (expected_ty < actual_ty) *) 
  | Iless_than_i of t * t (* not (expected_i < actual_i) *) 
  | Ilast of Ident.t (* [last x] is un-initialized *)
  | Ivar of Ident.t (* [x] is un-initialized *)
  | Ider of Ident.t (* equation [der x = ...] appear with no initialisation *)
exception Error of Location.t * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin
    match kind with
    | Iless_than(expected_ti, actual_ti) ->
        Format.eprintf
          "%aInitialization error: this expression \
           has type %a@ which should be less than@ %a.@."
          output_location loc
          Pinit.ptype expected_ti Pinit.ptype actual_ti
    | Iless_than_i(expected_i, actual_i) ->
        Format.eprintf
          "%aInitialization error: this expression \
           has type@ %a which should be less than@ %a.@."
          output_location loc
          Pinit.init expected_i Pinit.init actual_i
    | Ilast(n) ->
        Format.eprintf
          "%aInitialization error: the last value of %s \
           may not be well initialized.@."
          output_location loc
          (Ident.source n)
    | Ivar(n) ->
        Format.eprintf
          "%aInitialization error: the value of %s \
           may not be well initialized.@."
          output_location loc
          (Ident.source n)
    | Ider(n) ->
        Format.eprintf
          "%aInitialization error: the derivative of %s \
           is given but it is not initialized.@."
          output_location loc
          (Ident.source n)
  end;
  raise Misc.Error

let less_than loc actual_ti expected_ti =
  try
    Init.less actual_ti expected_ti
  with
    | Init.Clash _ -> error loc (Iless_than(actual_ti, expected_ti))

let less_for_last loc n actual_i expected_i =
  try
    Init.less_i actual_i expected_i
  with
    | Init.Clash _ -> error loc (Ilast(n))

let less_for_var loc n actual_ti expected_ti =
  try
    Init.less actual_ti expected_ti
  with
    | Init.Clash _ -> error loc (Ivar(n))

(* Build an environment from a typing environment *)
(* if [x] is defined by [init x = e] then
 *- [x] is initialized, that is [last x: 0]; otherwise [last x: 1] *)
let build_env l_env env =
  let open Deftypes in
  let entry x { t_sort; t_tys = { typ_body } } =
    match t_sort with
    | Sort_mem { m_init } ->
       let t_last = match m_init with | Eq | Decl _ -> izero | No -> ione in
       let t_tys =
         Definit.scheme (Init.skeleton_on_i (Init.new_var ()) typ_body) in
       { t_last; t_tys }
    | _ ->
       let t_tys = Definit.scheme (Init.skeleton typ_body) in
       { t_last = ione; t_tys } in
  Env.fold (fun n tentry acc -> Env.add n (entry n tentry) acc) l_env env

(* Build an environment from [env] by replacing the initialization *)
(* type of [x] by the initialization of its last value for all *)
(* [x in [shared\defnames] *)
(* this is because an absent definition for [x] in the current branch *)
(* is interpreted as if there were an equation [x = last x] *)
(* or [x = default_x] if [x] is declared with a default value *)
let last_env shared defnames env =
  let add n acc =
    let { t_tys = { typ_body } } = Env.find n env in
    Env.add n { t_tys = Definit.scheme (Init.fresh_on_i izero typ_body);
                t_last = izero } acc in
  let names = Defnames.cur_names Ident.S.empty defnames in
  let env_defnames =
    Ident.S.fold add (Ident.S.diff shared names) Env.empty in
  Env.append env_defnames env

(* Names from the set [last_names] are considered to be initialized *)
let add_last_to_env env last_names =
  let add n acc =
    let { t_tys = { typ_body } } = Env.find n env in
    Env.add n { t_tys = Definit.scheme (Init.fresh_on_i izero typ_body);
                t_last = izero } acc in
  let env_last_names =
    Ident.S.fold add last_names Env.empty in
  Env.append env_last_names env
            
(* find the potential initial handlers from an automaton. Returns them *)
(* and their complements *)
let split se_opt s_h_list =
  let statepat { desc } =
    match desc with
      | Estate0pat(id) | Estate1pat(id, _) -> id in
  let rec state acc { desc } =
    match desc with
    | Estate0(id) | Estate1(id, _) -> Ident.S.add id acc
    | Estateif(_, s1, s2) ->
       state (state acc s1) s2 in
  match se_opt with
  | Some(se) ->
     let acc = state Ident.S.empty se in
     List.partition (fun { s_state } -> Ident.S.mem (statepat s_state) acc)
       s_h_list
  | None -> (* the starting state is the first in the list *)
     match s_h_list with
     | [] -> assert false
     | s_h :: s_h_list -> [s_h], s_h_list

(** Check that partially defined names have a last value which is initialized *)
let initialized loc env shared =
  (* check that shared variable are initialialized *)
  let check n =
    let { t_tys = { typ_body } } =
      try Env.find n env with Not_found -> assert false in
    less_for_var loc n typ_body (Init.fresh_on_i izero typ_body) in
  Ident.S.iter check shared

(** Patterns *)
(* [pattern env p expected_ty] means that the type of [p] must be less *)
(* than [expected_ty] *)
let rec pattern env ({ pat_desc; pat_loc; pat_info } as p) expected_ti =
  let pat_typ = Typinfo.get_type pat_info in
  (* annotate the pattern with the initialization type *)
  p.pat_info <- Typinfo.set_init pat_info expected_ti;
  match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> ()
    | Evarpat(x) -> 
        let t_tys =
          try let { t_tys } = Env.find x env in t_tys
          with | Not_found -> assert false in
        let ti = Init.instance t_tys pat_typ in
        less_than pat_loc expected_ti ti
    | Econstr1pat(_, pat_list) ->
        let i = Init.new_var () in
        less_than pat_loc expected_ti (Init.skeleton_on_i i pat_typ);
        List.iter
          (fun p -> pattern_less_than_on_i env p i) pat_list
    | Etuplepat(pat_list) ->
        let ty_list = Init.filter_product expected_ti in
        List.iter2 (pattern env) pat_list ty_list
    | Erecordpat(l) -> 
        let i = Init.new_var () in
        List.iter
          (fun { arg } -> pattern_less_than_on_i env arg i) l
    | Etypeconstraintpat(p, _) -> pattern env p expected_ti
    | Eorpat(p1, p2) -> 
        pattern env p1 expected_ti;
        pattern env p2 expected_ti
    | Ealiaspat(p, n) -> 
        pattern env p expected_ti;
        let t_tys_n = 
          try let { t_tys } = Env.find n env in t_tys
          with | Not_found -> assert false in
        let ti = Init.instance t_tys_n pat_typ in
        less_than pat_loc expected_ti ti

and pattern_less_than_on_i env ({ pat_info } as pat) i =
  let pat_typ = Typinfo.get_type pat_info in
  let expected_ti = Init.skeleton_on_i i pat_typ in
  pattern env pat expected_ti
        
(** Match handler *)
let match_handlers body env m_h_list =
  let handler { m_pat; m_env; m_body; m_loc } =
    let env = build_env m_env env in
    ignore (body env m_body) in
  List.iter handler m_h_list

(** Present handler *)
let present_handlers scondpat body env p_h_list default_opt =
  let handler { p_cond; p_body; p_env; p_loc } =
    let env = build_env p_env env in
    scondpat env p_cond;
    ignore (body env p_body) in
  List.iter handler p_h_list;
  match default_opt with
  | NoDefault -> ()
  | Init(eq) | Else(eq) -> ignore (body env eq)

(** Automaton handler *)
let automaton_handlers scondpat exp_less_than_on_i leqs block_eq block_eq
      loc is_weak defnames env s_h_list se_opt =
  (* state *)
  let rec state env { desc } =
    match desc with
    | Estate0 _ -> ()
    | Estate1(_, e_list) -> 
       List.iter
         (fun e -> exp_less_than_on_i env e izero) e_list
    | Estateif(e, s1, s2) ->
       exp_less_than_on_i env e izero;
       state env s1;
       state env s2 in
     (* Compute the set of names defined by a state *)
     let cur_names_in_state b trans =
       let block acc { b_write } = Defnames.cur_names acc b_write in
       let escape acc { e_body } = block acc e_body in
       block (List.fold_left escape Ident.S.empty trans) b in
     (* transitions *)
     let escape shared env { e_cond; e_let; e_body; e_next_state; e_env } =
       let env = build_env e_env env in
       scondpat env e_cond;
       (* typing local definitions *)
       let env = leqs env e_let in
       (* then the body *)
       let env = block_eq shared env e_body in
       state env e_next_state in
     (* handler *)
     let handler shared env { s_state; s_let; s_body; s_trans; s_env } =
       (* remove from [shared] names defined in the current state *)
       let shared = Ident.S.diff shared (cur_names_in_state s_body s_trans) in
       let env = build_env s_env env in
       (* typing local definitions *)
       let env = leqs env s_let in
       (* then the body *)
       let env = block_eq shared env s_body in
       List.iter (escape shared env) s_trans in
     (* compute the set of shared names *)
     let shared = Defnames.cur_names Ident.S.empty defnames in
     (* do a special treatment for the potential initial states *)
     let first_s_h_list, remaining_s_h_list = split se_opt s_h_list in
     (* first type the initial branch *)
     List.iter (handler shared env) first_s_h_list;
     (* if the initial states have only weak transitions then all *)
     (* variables from [defined_names] do have a last value *)
     let cur_names acc { s_body = { b_write } } =
       Defnames.cur_names acc b_write in
     let last_names =
       List.fold_left cur_names Ident.S.empty first_s_h_list in
     let env =
       if is_weak then add_last_to_env env last_names else env in
     List.iter (handler shared env) remaining_s_h_list;
     (* every defined variable must be initialized *)
     initialized loc env shared;
     (* finaly check the initialisation *)
     ignore (Util.optional_map (state env) se_opt)

(** Initialization of an expression *)
let rec exp env ({ e_desc; e_info; e_loc } as e) =
  let e_typ = Typinfo.get_type e_info in
  let ti =
    match e_desc with
    | Econst _ | Econstr0 _ -> Init.skeleton_on_i (Init.new_var ()) e_typ
    | Eglobal { lname = lname } ->
       let { info } =
         try Modules.find_value lname with | Not_found -> assert false in
       Init.instance_of_global_value info e_typ
    | Evar(x) -> 
       let t_tys = try let { t_tys } = Env.find x env in t_tys 
                   with | Not_found -> print x in
       Init.instance t_tys e_typ
    | Elast { id } -> 
       begin try 
           (* [last x] is initialized only if an equation [init x = e] *)
           (* appears and [e] is also initialized *)
           let { t_tys = { typ_body } ; t_last } = Env.find id env in
           Init.fresh_on_i t_last typ_body
         with 
         | Not_found -> Init.skeleton_on_i ione e_typ end
    | Etuple(e_list) -> 
       product (List.map (exp env) e_list)
    | Econstr1 { arg_list } ->
       let i = Init.new_var () in
       List.iter (fun e -> exp_less_than_on_i env e i) arg_list;
       Init.skeleton_on_i i e_typ
    | Eop(op, e_list) -> operator env op e_typ e_list
    | Eapp { f; arg_list } ->
       app env (exp env f) arg_list
    | Erecord_access { arg } -> 
       let i = Init.new_var () in
       exp_less_than_on_i env arg i;
       Init.skeleton_on_i i e_typ
    | Erecord(l) -> 
       let i = Init.new_var () in
       List.iter (fun { arg } -> exp_less_than_on_i env arg i) l;
       Init.skeleton_on_i i e_typ
    | Erecord_with(e_record, l) -> 
       let i = Init.new_var () in
       exp_less_than_on_i env e_record i;
       List.iter (fun { arg } -> exp_less_than_on_i env arg i) l;
       Init.skeleton_on_i i e_typ
    | Etypeconstraint(e, _) -> exp env e
    | Elet(l, e_let) -> 
       let env = leq env l in
       exp env e_let
    | Efun(fe) -> funexp env fe
    | Epresent { handlers; default_opt } ->
       (* if [e] returns a tuple, all type element are synchronised, i.e., *)
       (* if one is un-initialized, the whole is un-initialized *)
       let ti = Init.skeleton_on_i (Init.new_var ()) e_typ in
       present_handler_exp_list env handlers default_opt ti;
       ti
    | Ematch { e; handlers } ->
       (* we force [e] to be always initialized. This is overly constraining *)
       (* but correct and simpler to justify *)
       exp_less_than_on_i env e izero;
       let ti = Init.skeleton_on_i (Init.new_var ()) e_typ in
       match_handler_exp_list env handlers ti;
       ti
    | Ereset(e_body, e_res) ->
       exp_less_than_on_i env e_res izero;
       exp env e_body
    | Eassert(e_body) -> exp env e_body
    | Eforloop _ ->
       Misc.not_yet_implemented "initialisation analysis for for-loops"
    | Esizeapp _ ->
       Misc.not_yet_implemented "initialisation analysis for size functions"
    | Elocal _ ->
       Misc.not_yet_implemented "initialisation analysis for local definitions" in
  (* annotate the expression with the initialization type *)
  e.e_info <- Typinfo.set_init e.e_info ti;
  ti
  
(** Typing an operator *)
and operator env op ty e_list =
  match op, e_list with
  | Eunarypre, [e] -> 
     (* input of a unit delay must be of type 0 *)
     exp_less_than_on_i env e izero; 
     Init.skeleton_on_i ione ty
  | Efby, [e1;e2] ->
     (* right input of a initialized delay must be of type 0 *)
     exp_less_than_on_i env e2 izero;
     exp env e1
  | Eminusgreater, [e1;e2] ->
     let t1 = exp env e1 in
     let _ = exp env e2 in
     t1
  | Eifthenelse, [e1; e2; e3] ->
     (* a conditional does not force all element to be initialized *)
     let i = Init.new_var () in
     exp_less_than_on_i env e1 i;
     exp_less_than_on_i env e2 i;
     exp_less_than_on_i env e3 i;
     Init.skeleton_on_i i ty
  | Eatomic, [e] ->
     let i = Init.new_var () in
     exp_less_than_on_i env e i;
     Init.skeleton_on_i i ty
  | Etest, [e] ->
     let i = Init.new_var () in
     exp_less_than_on_i env e i;
     Init.skeleton_on_i i ty
  | Eup, [e] ->
     exp_less_than_on_i env e izero;
     Init.skeleton_on_i izero ty
  | Eperiod, [e1; e2] ->
     exp_less_than_on_i env e1 izero;
     exp_less_than_on_i env e2 izero;
     Init.skeleton_on_i izero ty
  | Ehorizon, [e] ->
     exp_less_than_on_i env e izero;
     Init.skeleton_on_i izero ty
  | Eseq, [e1; e2] ->
     exp_less_than_on_i env e1 izero;
     exp_less_than_on_i env e2 izero;
     Init.skeleton_on_i izero ty
  | Erun _, [e1; e2] ->
     let t1 = exp env e1 in
     let ti1, ti2 = Init.filter_arrow t1 in
     exp_less_than env e2 ti1;
     ti2
  | _ -> assert false


(** Typing an application *)
and app env ti_fct arg_list =
  (* typing the list of arguments *)
  let rec args ti_fct = function
    | [] -> ti_fct
    | arg :: arg_list ->
       let ti1, ti2 = Init.filter_arrow ti_fct in
       exp_less_than env arg ti1;
       args ti2 arg_list in
  args ti_fct arg_list

and funexp env { f_kind; f_atomic; f_args; f_body; f_env; f_loc } =
  let env = build_env f_env env in
  let ti_list = List.map (arg env) f_args in
  let ti_res = result env f_body in
  let actual_ti = Init.funtype_list ti_list ti_res in
  (* for an atomic node, input/outputs get the same init type variable *)
  if f_atomic then
    let i = Init.new_var () in
    let expected_ti = Init.fresh_on_i i actual_ti in
    less_than f_loc actual_ti expected_ti;
    expected_ti
  else actual_ti

and arg h n_list = type_of_vardec_list h n_list

and exp_less_than_on_i env e expected_i =
  let actual_ti = exp env e in
  let e_typ = Typinfo.get_type e.e_info in
  less_than e.e_loc actual_ti (Init.skeleton_on_i expected_i e_typ);

and exp_less_than env ({ e_loc } as e) expected_ti =
  let actual_ty = exp env e in
  less_than e_loc actual_ty expected_ti

(** Checking equations *)
and equation_list env eq_list =
  List.iter (equation env) eq_list

and equation env
{ eq_desc = eq_desc; eq_loc = loc; eq_write = defnames } =
  match eq_desc with
  | EQeq(p, e) -> 
     let ti = exp env e in
     pattern env p ti
  | EQder { id; e; e_opt; handlers } ->
     (* e must be of type 0 *)
     exp_less_than_on_i env e izero;
     let ti_n, last = 
        try let { t_tys = { typ_body }; t_last } = Env.find id env in 
          typ_body, t_last 
        with | Not_found -> assert false in
      exp_less_than env e ti_n;
      let e_typ = Typinfo.get_type e.e_info in
      less_than loc ti_n (Init.skeleton_on_i Init.izero e_typ);
      (match e_opt with
       | Some(e0) -> exp_less_than_on_i env e0 izero
       | None -> less_for_last loc id last izero);
      present_handler_exp_list env handlers NoDefault ti_n 
  | EQinit(n, e) ->
      exp_less_than_on_i env e izero
  | EQemit(n, e_opt) ->
      let ti_n = 
        try let { t_tys = { typ_body } } = Env.find n env in typ_body
        with | Not_found -> assert false in
      less_than loc ti_n (Init.atom izero);
      Util.optional_unit
        (fun i e -> exp_less_than_on_i env e i) izero e_opt
  | EQautomaton {is_weak; handlers; state_opt } ->
     automaton_handler_eq_list
       loc is_weak defnames env handlers state_opt
  | EQif { e; eq_true; eq_false } ->
     exp_less_than_on_i env e izero;
     let shared = Defnames.cur_names Ident.S.empty defnames in
     let env1 = last_env shared eq_true.eq_write env in
     equation env1 eq_true;
     let env2 = last_env shared eq_false.eq_write env in
     equation env2 eq_false
  | EQmatch { e; handlers } ->
     exp_less_than_on_i env e izero;
     let shared = Defnames.cur_names Ident.S.empty defnames in
     match_handler_eq_list shared env handlers;
     (* every defined variable must be initialized *)
     initialized loc env shared
  | EQpresent { handlers; default_opt } ->
     let shared = Defnames.cur_names Ident.S.empty defnames in
     present_handler_eq_list shared env handlers default_opt;
     (* every defined variable must be initialized *)
     initialized loc env shared
  | EQreset(eq, e) -> 
     exp_less_than_on_i env e izero;
     equation env eq
  | EQand { eq_list } -> equation_list env eq_list
  | EQlocal(b_eq) ->
     ignore (block_eq Ident.S.empty env b_eq)
  | EQlet(l_eq, eq) ->
     let env = leq env l_eq in equation env eq
  | EQassert(e) -> exp_less_than_on_i env e izero 
  | EQempty -> ()
  | EQforloop _ ->
     Misc.not_yet_implemented "initialisation analysis for for-loops"
  | EQsizefun _ ->
     Misc.not_yet_implemented "initialisation analysis for size functions"
       
(* typing rule for a present statement *)
and present_handler_eq_list shared env p_h_list default_opt =
  let equation env ({ eq_write } as eq) =
    let env = last_env shared eq_write env in
    equation env eq in
  present_handlers scondpat equation env p_h_list default_opt

and present_handler_exp_list env p_h_list default_opt ti =
  let exp env e = exp_less_than env e ti in
  present_handlers scondpat exp env p_h_list default_opt

and match_handler_eq_list shared env m_h_list =
  let equation env ({ eq_write } as eq) =
    let env = last_env shared eq_write env in
    equation env eq in
  match_handlers equation env m_h_list

and match_handler_exp_list env m_h_list ti =
  let exp env e = exp_less_than env e ti in
  match_handlers exp env m_h_list

and automaton_handler_eq_list loc is_weak defnames env s_h_list se_opt =
  automaton_handlers
    scondpat exp_less_than_on_i leqs block_eq block_eq
    loc is_weak defnames env s_h_list se_opt

and block_eq shared env { b_loc; b_body; b_env; b_write } =
  (* shared variables depend on their last causality *)
  let env = last_env shared b_write env in
  let env = build_env b_env env in
  equation env b_body;
  env

and leq env { l_eq; l_env } =
  (* First extend the typing environment *)
  let env = build_env l_env env in
  (* then type the body *)
  equation env l_eq;
  env

and leqs env l = List.fold_left leq env l
               
(* we force that the signal pattern be initialized. E.g.,
 *- [present s(x) -> ...] gives the type 0 to s and x *)
and scondpat env { desc = desc } =
  match desc with
  | Econdand(sc1, sc2) | Econdor(sc1, sc2) -> 
     scondpat env sc1; scondpat env sc2
  | Econdon(sc1, e) ->
     scondpat env sc1;
     exp_less_than_on_i env e izero
  | Econdexp(e) | Econdpat(e, _) -> 
     exp_less_than_on_i env e izero

(* Computes the result type for [returns (...) eq] *)
and type_of_vardec_list env n_list =
  let type_of_vardec ({ var_name; var_info } as v) =
    let { t_tys } = try Env.find var_name env with Not_found -> print var_name in
    let ty = Typinfo.get_type var_info in
    let ti = Init.instance t_tys ty in
    (* annotate with the initialization type *)
    v.var_info <- Typinfo.set_init var_info ti;
    ti in
  let ti_list = List.map type_of_vardec n_list in
  match ti_list with
  | [] -> Init.atom(Init.new_var ())
  | [ti] -> ti  
  | _ -> Init.product ti_list

and result env ({ r_desc; r_info } as r) =
  let ti =
    match r_desc with
    | Exp(e) -> exp env e
    | Returns({ b_vars } as b) ->
       let env = block_eq Ident.S.empty env b in
       type_of_vardec_list env b_vars in
  (* type annotation *)
  r.r_info <- Typinfo.set_init r_info ti;
  ti
 
let implementation ff impl =
  try
    match impl.desc with
    | Eopen _ | Etypedecl _ -> ()
    | Eletdecl { d_leq } ->
       (* generalisation is done only for global declarations *)
       Misc.push_binding_level ();
       let env = leq Env.empty d_leq in
       Misc.pop_binding_level ();
       let env = gen_decl env in
       Env.iter
         (fun name { t_tys } ->
           Global.set_init
             (Modules.find_value (Lident.Name(Ident.source name))) t_tys)
         env;
       (* output the signature *)
       if !Misc.print_initialization_types
       then
         Env.iter
           (fun name { t_tys } ->
             Pinit.declaration ff (Ident.source name) t_tys) env
  with
  | Error(loc, kind) -> message loc kind
                          
(* the main entry function *)
let program ff ({ p_impl_list } as p) =
  List.iter (implementation ff) p_impl_list;
  p
