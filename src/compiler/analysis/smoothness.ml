(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2026 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* smoothness analysis. It is a variation of the initialisation analysis *)
(* See paper by Colaco and Pouzet, STTT'2004 *)

(* this analysis gives *)
(* three possible basic types to a signal expression [e] *)
(* H |- e : s where s ::= 0 | 1/2 | 1 or a variable [a] *)
(* with 0 <= 1/2 <= 1 and possible order between variables and [s] *)
(* [s] informs about the status of the signal during integration *)
(* that is, out of zero-crossing instants *)
(* 0 : the signal is surely constant during integration (do not depend *)
(*     on the solver *)
(* 1/2 : the signal may change during integration *)
(* (it may depend on the solver *)
(* 1, otherwise *)
(* Principle:
 *- 1/ If [x] is defined by an equation [...x... = e] activated continuously
 *- then h(x) <= 1/2 and 1 <= h(last x) where [h] is the typing environment.
 *- during a discrete-step, all signals get type [0] *)

(* Signals on floatting-point arithmetic get polymorphic types *)
(* whereas integer values are forced to be constant during integration
 *- as well as conditions in if/then/else and all control decisions
 *- (present, until/unless conditions in automata)
 *-
 *- val (Stdlib.+.), (Stdlib.-.), ( Stdlib.*. ), (Stdlib./.), (Stdlib./.)
 *-   : 'a -> 'a -> 'a
 *- val (if): 0 -> 'a -> 'a -> 'a
 *- val fix_der : 1 -> (1/2 -> 1/2) -> 1/2
 *- that is: fix_der x0 f = let rec der x = f(x) init x0 in x
 *- the signal to be integrated can only change smoothly
 *- val floor, int_of_float : 0 -> 0
 *- more generally, by default, imported primitives have a smooth type
 *- that force their entries to have type [0]
 *)
open Misc
open Ident
open Global
open Zelus
open Location
open Deftypes
open Defsmooth
open Tsmooth

(* Set the smooth type for arithmetic primitives (+.), ( *.), (/.) and (-.) *)
let add_type_for_polymorphic_primitives_in_stdlib () =
  let tys =
    (* build the type signature: 'a. 'a -> 'a -> 'a *)
    let i = Defsmooth.make_var () in
    let ty = Tsmooth.funtype_list
               [Tsmooth.atom i; Tsmooth.atom i] (Tsmooth.atom i) in
    { typ_vars = [i]; typ_rel = []; typ_body = ty } in
  List.iter
    (fun n -> let info = Modules.find_value (Modname { qual = "Stdlib"; id = n }) in
              Global.set_smooth info tys)
    ["+."; "*."; "/."; "-."]

let print x = Misc.internal_error "unbound" Printer.name x

let find x env = try Env.find x env with Not_found -> print x

(* Main error message *)
type error =
  | Iless_than of ti * ti (* not (expected_ty < actual_ty) *) 
  | Iless_than_i of t * t (* not (expected_i < actual_i) *) 

exception Error of Location.t * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin
    match kind with
    | Iless_than(expected_ti, actual_ti) ->
        Format.eprintf
          "%aSmoothness error: this expression \
           has type %a@ which should be less than@ %a.@."
          output_location loc
          Psmooth.ptype expected_ti Psmooth.ptype actual_ti
    | Iless_than_i(expected_i, actual_i) ->
        Format.eprintf
          "%aSmoothness error: this expression \
           has type@ %a which should be less than@ %a.@."
          output_location loc
          Psmooth.smooth expected_i Psmooth.smooth actual_i
   end;
  raise Misc.Error

let less_than loc actual_ti expected_ti =
  try
    Tsmooth.less actual_ti expected_ti
  with
    | Tsmooth.Clash _ -> error loc (Iless_than(actual_ti, expected_ti))

let less_than_i loc actual_t expected_t =
  try
    Tsmooth.less_i actual_t expected_t
  with
    | Tsmooth.Clash _ -> error loc (Iless_than_i(actual_t, expected_t))

(* Build an environment from a typing environment *)
(* [local x in ... x = ...  ... last x ... der x = ...] *)
(* [x: ti_x] and [last x: ti_x[1/2]] *)
let build_env loc l_env env =
  let open Deftypes in
  let entry x { t_sort; t_tys = { typ_body } } =
    let i = Tsmooth.new_var () in
    let t_tys =
      Defsmooth.scheme (Tsmooth.skeleton_on_i i typ_body) in
    let t_last =
      match t_sort with
      | Sort_mem { m_mkind = Some(Cont) } ->
         (* [x] is defined by an ODE [der x = ...]. During integration *)
         (* [x = last x] and they get the same type [1/2] *)
         Some(Tsmooth.ihalf)
      | Sort_mem { m_last = true } ->
         (* a fresh type variable is used for [last x]. If [x] is defined *)
         (* by an equation [...x... = e] that is activated during integration *)
         (* then [x] should have a type that is less than [1/2] *)
         (* [last x] a type [1] *)
         Some(Tsmooth.new_var ())
      | _ -> None in
    { t_tys; t_last } in
  Env.fold (fun n tentry acc -> Env.add n (entry n tentry) acc) l_env env

(* Computes the type from a vardec list *)
let type_of_n_list type_of n_list =
  let ti_list = List.map type_of n_list in
  match ti_list with
  | [] -> Tsmooth.atom Tsmooth.izero
  | [ti] -> ti
  | _ -> Tsmooth.product ti_list

(* Patterns *)
(* [pattern env p expected_ti] means that the type of [p] must be greater *)
(* than [expected_ti] *)
let pattern is_zero env pat expected_ti =
  let rec pattern { pat_desc; pat_loc; pat_info } expected_ti =
    let pat_typ = Typinfo.get_type pat_info in
    match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> ()
    | Evarpat(x) -> 
       let ti, t_last =
         let { t_tys = { typ_body = ti }; t_last } = find x env in ti, t_last in
       less_than pat_loc expected_ti ti;
       (* when [not is_zero and [last x] is used] then *)
       (* [env(x) <= 1/2] and [1 <= env(last x)] *)
       (* no constraint otherwise *)
       set_x_and_last_x pat_loc is_zero pat_info ti t_last
    | Econstr1pat(_, pat_list) | Earraypat(pat_list) ->
       (* a construct is considered to be strict *)
       let i = Tsmooth.new_var () in
       less_than pat_loc expected_ti (Tsmooth.skeleton_on_i i pat_typ);
       List.iter
         (fun p -> pattern_less_than_on_i is_zero env p i) pat_list
    | Etuplepat(pat_list) ->
       let ty_list = Tsmooth.filter_product expected_ti in
       List.iter2 pattern pat_list ty_list
    | Erecordpat(l) -> 
       let i = Tsmooth.new_var () in
       List.iter
         (fun { arg } -> pattern_less_than_on_i is_zero env arg i) l
    | Etypeconstraintpat(p, _) -> pattern p expected_ti
    | Eorpat(p1, p2) -> 
       pattern p1 expected_ti;
       pattern p2 expected_ti
    | Ealiaspat(p, n) -> 
       pattern p expected_ti;
       let { t_tys; t_last } = find n env in
       let ti = Tsmooth.instance t_tys pat_typ in
       less_than pat_loc expected_ti ti;
       (* when [not is_zero and [last x] is used] then *)
       (* env(x) <= 1/2 and 1 <= env(last x) *)
       (* no constraint otherwise *)
       set_x_and_last_x pat_loc is_zero pat_info ti t_last

  and set_x_and_last_x pat_loc is_zero pat_info ti t_last =
    match t_last with
    | Some(i) when not is_zero ->
       let pat_typ = Typinfo.get_type pat_info in
       let ti_half = Tsmooth.skeleton_on_i ihalf pat_typ in
       less_than_i pat_loc ione i;
       less_than pat_loc ti ti_half
    | _ -> ()

  and pattern_less_than_on_i is_zero env ({ pat_info } as pat) i =
    let pat_typ = Typinfo.get_type pat_info in
    let expected_ti = Tsmooth.skeleton_on_i i pat_typ in
    pattern pat expected_ti in

  pattern pat expected_ti
        
(** Match handler *)
let match_handlers body is_zero env m_h_list =
  let handler { m_pat; m_env; m_body; m_zero; m_loc } =
    let env = build_env m_pat.pat_loc m_env env in
    (* the field [m_zero] has been set during typing *)
    ignore (body (is_zero || m_zero) env m_body) in
  List.iter handler m_h_list

(** Present handler *)
let present_handlers scondpat body is_zero env p_h_list default_opt =
  let handler { p_cond; p_body; p_env; p_zero; p_loc } =
    let env = build_env p_loc p_env env in
    scondpat is_zero env p_cond;
    (* the field [p_zero] has been set during typing *)
    ignore (body (is_zero || p_zero) env p_body) in
  List.iter handler p_h_list;
  match default_opt with
  | NoDefault -> ()
  | Init(eq) | Else(eq) -> ignore (body is_zero env eq)

(** Automaton handler *)
let automaton_handlers scondpat exp_less_than_on_i leqs block_eq block_eq
      loc is_zero is_weak defnames env s_h_list se_opt =
  (* state *)
  let rec state is_zero env { desc } =
    match desc with
    | Estate0 _ -> ()
    | Estate1(_, e_list) -> 
       List.iter
         (fun e -> exp_less_than_on_i is_zero env e izero) e_list
    | Estateif(e, s1, s2) ->
       exp_less_than_on_i is_zero env e izero;
       state is_zero env s1;
       state is_zero env s2 in
  (* transitions *)
  let escape is_zero env
        { e_cond; e_let; e_body; e_next_state; e_zero; e_env } =
    let env = build_env e_cond.loc e_env env in
    scondpat is_zero env e_cond;
    (* typing local definitions *)
    let env = leqs (is_zero || e_zero) env e_let in
    (* then the body *)
    let env = block_eq (is_zero || e_zero) env e_body in
    state is_zero env e_next_state in
  (* handler *)
  let handler is_zero env { s_state; s_let; s_body; s_trans; s_env } =
    let env = build_env s_state.loc s_env env in
    (* typing local definitions *)
    let env = leqs is_zero env s_let in
    (* then the body *)
    let env = block_eq is_zero env s_body in
    List.iter (escape is_zero env) s_trans in
  List.iter (handler is_zero env) s_h_list;
  (* finaly check the initialisation *)
  ignore (Util.optional_map (state is_zero env) se_opt)

(* Typing the declaration of variables. *)
let rec vardec_list is_zero env v_list =
  List.iter (vardec is_zero env) v_list

and vardec is_zero env ({ var_name; var_default; var_init }) =
  (* every initialization and default value must be well initialized *)
  Util.optional_unit
    (fun env e -> exp_less_than_on_i is_zero env e Tsmooth.izero)
    env var_init;
   
(* analysis of an expression *)
and exp is_zero env { e_desc; e_info; e_loc } =
  let e_typ = Typinfo.get_type e_info in
  let ti =
    match e_desc with
    | Econst _ | Econstr0 _ -> Tsmooth.skeleton_on_i (Tsmooth.new_var ()) e_typ
    | Eglobal { lname = lname } ->
       let { info } =
         try Modules.find_value lname with | Not_found -> assert false in
       let ti = Tsmooth.instance_of_global_value info e_typ in
       (* in a discrete-time context the basic type is [0] *)
       if is_zero then Tsmooth.zero_type ti else ti
    | Evar(x) -> 
       let { t_tys } = find x env in
       Tsmooth.instance t_tys e_typ
    | Elast { id } -> 
       let { t_tys = { typ_body } ; t_last } = find id env in
       let ty =
         match t_last with
         | None -> assert false | Some(i) -> Tsmooth.fresh_on_i i typ_body in
       ty
    | Etuple(e_list) -> 
       product (List.map (exp is_zero env) e_list)
    | Econstr1 { arg_list } ->
       let i = Tsmooth.new_var () in
       List.iter (fun e -> exp_less_than_on_i is_zero env e i) arg_list;
       Tsmooth.skeleton_on_i i e_typ
    | Eop(op, e_list) -> operator is_zero env op e_typ e_list
    | Eapp { f; arg_list } ->
       let ti_f = exp is_zero env f in
       app is_zero env ti_f arg_list
    | Erecord_access { arg } -> 
       let i = Tsmooth.new_var () in
       exp_less_than_on_i is_zero env arg i;
       Tsmooth.skeleton_on_i i e_typ
    | Erecord(l) -> 
       let i = Tsmooth.new_var () in
       List.iter (fun { arg } -> exp_less_than_on_i is_zero env arg i) l;
       Tsmooth.skeleton_on_i i e_typ
    | Erecord_with(e_record, l) -> 
       let i = Tsmooth.new_var () in
       exp_less_than_on_i is_zero env e_record i;
       List.iter (fun { arg } -> exp_less_than_on_i is_zero env arg i) l;
       Tsmooth.skeleton_on_i i e_typ
    | Etypeconstraint(e, _) -> exp is_zero env e
    | Elet(l, e_let) -> 
       let env = leq is_zero env l in
       exp is_zero env e_let
    | Efun(fe) -> funexp is_zero env fe
    | Epresent { handlers; default_opt } ->
       (* we force the conditions to be of type [0] *)
       (* if the output [e] is a structure, all components are synchronised *)
       let ti = Tsmooth.skeleton_on_i (Tsmooth.new_var ()) e_typ in
       present_handler_exp_list is_zero env handlers default_opt ti;
       ti
    | Ematch { e; handlers } ->
       (* we force [e] to be of type [0] *)
       exp_less_than_on_i is_zero env e izero;
       let ti = Tsmooth.skeleton_on_i (Tsmooth.new_var ()) e_typ in
       match_handler_exp_list is_zero env handlers ti;
       ti
    | Ereset(e_body, e_res) ->
       exp_less_than_on_i is_zero env e_res izero;
       exp is_zero env e_body
    | Eassert { a_body } -> exp is_zero env a_body
    | Elocal(b_eq, e_body) ->
       let env = block_eq is_zero env b_eq in
       exp is_zero env e_body
    | Eforloop(fe) -> forloop_exp e_loc is_zero env fe
    | Esizeapp { f } -> exp is_zero env f in
  ti
  
(* Typing an operator *)
and operator is_zero env op ty e_list =
  let i = Tsmooth.new_var () in
  match op, e_list with
  | Eunarypre, [e] -> 
     (* input of a unit delay must be of type 0 *)
     exp_less_than_on_i is_zero env e izero; 
     Tsmooth.skeleton_on_i izero ty
  | Efby, [e1;e2] ->
     (* right input of a initialized delay must be of type 0 *)
     exp_less_than_on_i is_zero env e2 izero;
     exp is_zero env e1
  | Eminusgreater, [e1;e2] ->
     let t1 = exp is_zero env e1 in
     let _ = exp is_zero env e2 in
     t1
  | Eifthenelse, [e1; e2; e3] ->
     (* a conditional forces the first argument to be constant *)
     exp_less_than_on_i is_zero env e1 izero;
     let i = Tsmooth.new_var () in
     exp_less_than_on_i is_zero env e2 i;
     exp_less_than_on_i is_zero env e3 i;
     Tsmooth.skeleton_on_i i ty
  | Eup _, [e] ->
     exp_less_than_on_i is_zero env e ihalf;
     Tsmooth.skeleton_on_i izero ty
  | Einitial, [] ->
     Tsmooth.skeleton_on_i izero ty
  | (Edisc | Ehorizon _), [e] ->
     exp_less_than_on_i is_zero env e ihalf;
     Tsmooth.skeleton_on_i izero ty
  | Eperiod, [e1; e2] ->
     exp_less_than_on_i is_zero env e1 izero;
     exp_less_than_on_i is_zero env e2 izero;
     Tsmooth.skeleton_on_i izero ty
  | Eseq, [e1; e2] ->
     exp_less_than_on_i is_zero env e1 izero;
     exp_less_than_on_i is_zero env e2 izero;
     Tsmooth.skeleton_on_i izero ty
  | Eatomic, [e] ->
     exp_less_than_on_i is_zero env e i;
     Tsmooth.skeleton_on_i i ty
  | Etest, [e] ->
     let i = Tsmooth.new_var () in
     exp_less_than_on_i is_zero env e i;
     Tsmooth.skeleton_on_i i ty
  | Erun _, [e1; e2] ->
     let t1 = exp is_zero env e1 in
     let ti1, ti2 = Tsmooth.filter_arrow t1 in
     exp_less_than is_zero env e2 ti1;
     ti2
  | Earray(op), e_list -> array_operator is_zero env op ty e_list
  | _ -> assert false

and array_operator is_zero env op ty e_list =
  (* the type of the result *)
  match op, e_list with
  | Earray_list, e_list ->
     let i = Tsmooth.new_var () in
     List.iter (fun e -> exp_less_than_on_i is_zero env e i) e_list;
     Tsmooth.skeleton_on_i i ty
  | (Econcat | Eget), [e1; e2] ->
     let i = Tsmooth.new_var () in
     exp_less_than_on_i is_zero env e1 i;
     exp_less_than_on_i is_zero env e2 i;
     Tsmooth.skeleton_on_i i ty
  | (Eget_with_default | Eslice _ | Eupdate), l ->
     let i = Tsmooth.new_var () in
     List.iter (fun e -> exp_less_than_on_i is_zero env e i) l;
     Tsmooth.skeleton_on_i i ty
  | (Etranspose | Ereverse | Eflatten), [e1] ->
     let i = Tsmooth.new_var () in
     exp_less_than_on_i is_zero env e1 i;
     Tsmooth.skeleton_on_i i ty
  | _ -> assert false

(** Typing an application *)
and app is_zero env ti_fct arg_list =
  (* typing the list of arguments *)
  let rec args ti_fct = function
    | [] -> ti_fct
    | arg :: arg_list ->
       let ti1, ti2 = Tsmooth.filter_arrow ti_fct in
       exp_less_than is_zero env arg ti1;
       args ti2 arg_list in
  args ti_fct arg_list

and funexp is_zero
    env { f_kind; f_atomic; f_args; f_body; f_env; f_loc } =
  let expected_body_k = Interface.kindtype f_kind in
  let is_zero = Types.is_discrete_kind expected_body_k in
  let env = build_env f_loc f_env env in
  let ti_list = List.map (arg env) f_args in
  let ti_res = result is_zero env f_body in
  let actual_ti = Tsmooth.funtype_list ti_list ti_res in
  (* for an atomic node, input/outputs get the same smooth type variable *)
  if f_atomic then
    let i = Tsmooth.new_var () in
    let expected_ti = Tsmooth.fresh_on_i i actual_ti in
    less_than f_loc actual_ti expected_ti;
    expected_ti
  else actual_ti

and arg env n_list = type_of_vardec_list env n_list

and exp_less_than_on_i is_zero env e expected_i =
  let actual_ti = exp is_zero env e in
  let e_typ = Typinfo.get_type e.e_info in
  less_than e.e_loc actual_ti (Tsmooth.skeleton_on_i expected_i e_typ);

and exp_less_than is_zero env ({ e_loc } as e) expected_ti =
  let actual_ty = exp is_zero env e in
  less_than e_loc actual_ty expected_ti

(** Checking equations *)
and equation_list is_zero env eq_list =
  List.iter (equation is_zero env) eq_list

and equation is_zero env { eq_desc; eq_loc; eq_write } =
  match eq_desc with
  | EQeq(p, e) -> 
     let ti = exp is_zero env e in
     (* [ti <= env(p)] *)
     (* if [not is_zero] then [env(x) <= 1/2 /\ 1 <= env(last x)] *)
     pattern is_zero env p ti
  | EQder { id; e; e_opt; handlers } ->
     (* e must be of type <= 1/2 *)
     exp_less_than_on_i is_zero env e ihalf;
     let { t_tys = { typ_body }; t_last } = find id env in 
     let e_typ = Typinfo.get_type e.e_info in
     less_than eq_loc typ_body (Tsmooth.skeleton_on_i Tsmooth.ihalf e_typ);
     (* debug *)
     (* TODO: *)
     Format.eprintf "%a\n" Psmooth.ptype typ_body;
     (match e_opt with
      | Some(e0) -> exp_less_than_on_i is_zero env e0 izero
      | None -> ());
     present_handler_exp_list is_zero env handlers NoDefault typ_body 
  | EQinit(n, e) ->
      exp_less_than_on_i true env e izero
  | EQemit(n, e_opt) ->
      let { t_tys = { typ_body } } = find n env in 
      less_than eq_loc typ_body (Tsmooth.atom izero);
      Util.optional_unit
        (fun i e -> exp_less_than_on_i is_zero env e i) izero e_opt
  | EQautomaton {is_weak; handlers; state_opt } ->
     automaton_handler_eq_list
       eq_loc is_zero is_weak eq_write env handlers state_opt
  | EQif { e; eq_true; eq_false } ->
     exp_less_than_on_i is_zero env e izero;
     equation is_zero env eq_true;
     equation is_zero env eq_false
  | EQmatch { e; handlers } ->
     exp_less_than_on_i is_zero env e izero;
     let shared = Defnames.cur_names Ident.S.empty eq_write in
     match_handler_eq_list is_zero shared env handlers
  | EQpresent { handlers; default_opt } ->
     let shared = Defnames.cur_names Ident.S.empty eq_write in
     present_handler_eq_list is_zero shared env handlers default_opt
  | EQreset(eq, e) -> 
     exp_less_than_on_i is_zero env e izero;
     equation is_zero env eq
  | EQand { eq_list } -> equation_list is_zero env eq_list
  | EQlocal(b_eq) ->
     ignore (block_eq is_zero env b_eq)
  | EQlet(l_eq, eq) ->
     let env = leq is_zero env l_eq in equation is_zero env eq
  | EQassert { a_body } -> exp_less_than_on_i is_zero env a_body izero 
  | EQempty -> ()
  | EQforloop(f_eq) -> forloop_eq eq_loc is_zero env f_eq
  | EQsizefun(f_size) -> sizefun_t is_zero env f_size
       
(* typing rule for a present statement *)
and present_handler_eq_list is_zero shared env p_h_list default_opt =
  present_handlers scondpat equation is_zero env p_h_list default_opt

and present_handler_exp_list is_zero env p_h_list default_opt ti =
  let exp is_zero env e = exp_less_than is_zero env e ti in
  present_handlers scondpat exp is_zero env p_h_list default_opt

and match_handler_eq_list is_zero shared env m_h_list =
  let equation is_zero env eq =
    equation is_zero env eq in
  match_handlers equation is_zero env m_h_list

and match_handler_exp_list is_zero env m_h_list ti =
  let exp is_zero env e = exp_less_than is_zero env e ti in
  match_handlers exp is_zero env m_h_list

and automaton_handler_eq_list
      loc is_zero is_weak defnames env s_h_list se_opt =
  automaton_handlers
    scondpat exp_less_than_on_i leqs block_eq block_eq
    loc is_zero is_weak defnames env s_h_list se_opt

and block_eq is_zero env { b_loc; b_body; b_env } =
  let env = build_env b_loc b_env env in
  equation is_zero env b_body;
  env

and leq is_zero env { l_eq; l_env; l_loc } =
  (* First extend the typing environment *)
  let env = build_env l_loc l_env env in
  (* then type the body *)
  equation is_zero env l_eq;
  env

and leqs is_zero env l = List.fold_left (leq is_zero) env l
               
(* we force that the signal pattern be initialized. E.g.,
 *- [present s(x) -> ...] gives the type 0 to s and x *)
and scondpat is_zero env { desc } =
  match desc with
  | Econdand(sc1, sc2) | Econdor(sc1, sc2) -> 
     scondpat is_zero env sc1; scondpat is_zero env sc2
  | Econdon(sc1, e) ->
     scondpat is_zero env sc1;
     exp_less_than_on_i is_zero env e izero
  | Econdexp(e) | Econdpat(e, _) -> 
     exp_less_than_on_i is_zero env e izero

(* Computes the result type for [returns (...) eq] *)
and type_of_vardec env { var_name; var_info } =
  let { t_tys = { typ_body = ti } } = find var_name env in
  ti

and type_of_vardec_list env n_list = 
  type_of_n_list (type_of_vardec env) n_list

and result is_zero env { r_desc; r_info } =
  let ti =
    match r_desc with
    | Exp(e) -> exp is_zero env e
    | Returns({ b_vars } as b) ->
       let env = block_eq is_zero env b in
       type_of_vardec_list env b_vars in
  ti
 
(* Typing of a for loop *)
and forloop_exp loc is_zero env
      { for_env; for_size; for_kind; for_input; for_let; for_body } =
  (* inputs, index and outputs must be initialized *)
  for_size_t is_zero env for_size;
  List.iter (for_input_t is_zero env) for_input;
  let env = build_env loc for_env env in
  (* typing local definitions *)
  let env = leqs is_zero env for_let in
  for_kind_t is_zero env for_kind;
  for_exp_t loc is_zero env for_body

and for_exp_t loc is_zero env for_exp =
  match for_exp with
  | Forexp { exp = e; default } ->
     let ty = Typinfo.get_type e.e_info in
     let ti_e = Tsmooth.skeleton_on_i Tsmooth.izero ty in
     exp_less_than is_zero env e ti_e;
     Util.optional_with_default
       (fun e -> exp_less_than_on_i is_zero env e Tsmooth.izero)
       () default;
     ti_e
  | Forreturns { r_returns; r_block; r_env } ->
     List.iter (for_vardec is_zero env) r_returns;
     let env = build_env loc r_env env in
     let _ = block_eq is_zero env r_block in
     type_of_for_vardec_list env r_returns

and for_vardec is_zero env { desc = { for_vardec } } =
  vardec is_zero env for_vardec

and type_of_for_vardec_list env n_list =
  let type_of { desc = { for_vardec } } =
    type_of_vardec env for_vardec in
  type_of_n_list type_of n_list

(* sizes must be initialized *)
and for_size_t is_zero env for_size_opt =
  Util.optional_unit
    (fun env { for_size_exp } ->
      exp_less_than_on_i is_zero env for_size_exp Tsmooth.izero)
    env for_size_opt

and for_kind_t is_zero env for_kind =
  match for_kind with
  | Kforeach -> ()
  | Kforward(for_exit_opt) ->
     Util.optional_unit (for_exit_t is_zero) env for_exit_opt

and for_exit_t is_zero env { for_exit } =
  exp_less_than_on_i is_zero env for_exit Tsmooth.izero

and for_index_t for_index_opt =
  Util.optional_with_default
    (fun id ->
      Env.singleton id { t_last = None; t_tys = Defsmooth.scheme (atom izero) })
    Env.empty for_index_opt

and for_eq_t loc is_zero env { for_out; for_block; for_out_env } =
  (* outputs must be initialized *)
  List.iter (for_out_t is_zero env) for_out;
  let env = build_env loc for_out_env env in
  let _ = block_eq is_zero env for_block in
  ()

and for_out_t
    is_zero env { desc = { for_locals; for_ext; for_info }; loc; } =
  (* find the type of [for_ext] in [env] *)
  let { t_tys = { typ_body = ti } } = find for_ext env in
  let typ = Typinfo.get_type for_info in
  less_than loc ti (Tsmooth.skeleton_on_i Tsmooth.izero typ);

  match for_locals with
  | OAcc { for_acc = x } | OArray { for_item = x } ->
    (* every initialization and default value must be well initialized *)
    Util.optional_unit
      (fun env e -> exp_less_than_on_i is_zero env e Tsmooth.izero)
      env x.for_init;
    Util.optional_unit
      (fun env e -> exp_less_than_on_i is_zero env e Tsmooth.izero)
      env x.for_default;

(* all inputs must be well-initialized *)
and for_input_t is_zero env { desc; loc } =
  match desc with
  | Einput { e; by } ->
     exp_less_than_on_i is_zero env e Tsmooth.izero;
     Util.optional_unit 
       (fun env e -> exp_less_than_on_i is_zero env e Tsmooth.izero)
       env by
  | Eindex { e_left; e_right } ->
     exp_less_than_on_i is_zero env e_left Tsmooth.izero;
     exp_less_than_on_i is_zero env e_right Tsmooth.izero

(* Typing of a for loop *)
and forloop_eq loc is_zero env
       { for_env; for_size; for_kind; for_input; for_let; for_body } =
  (* inputs, index and outputs must be initialized *)
  for_size_t is_zero env for_size;
  (* check that all inputs are initialized *)
  List.iter (for_input_t is_zero env) for_input;
  let env = build_env loc for_env env in
  (* typing local definitions *)
  let env = leqs is_zero env for_let in
  for_kind_t is_zero env for_kind;
  for_eq_t loc is_zero env for_body

and sizefun_t is_zero env { sf_id; sf_id_list; sf_e; sf_loc } =
  let env_sizes =
    List.fold_left 
      (fun acc id -> 
        Env.add id 
          { t_last = None; t_tys = Defsmooth.scheme (Tsmooth.atom izero) } acc) 
      Env.empty sf_id_list in
  let env = Env.append env_sizes env in
  let actual_ti = exp is_zero env sf_e in
  (* check that [sf_id] can get type [actual_ti] *)
  let { t_tys = { typ_body = expected_ti } } = find sf_id env in
  less_than sf_loc expected_ti actual_ti

let implementation ff impl =
  try
    match impl.desc with
    | Eopen _ | Etypedecl _ -> ()
    | Eletdecl { d_leq } ->
       (* generalisation is done only for global declarations *)
       Misc.push_binding_level ();
       (* [is_zero = false] for top level definitions *)
       let env = leq false Env.empty d_leq in
       Misc.pop_binding_level ();
       let env = gen_decl env in
       Env.iter
         (fun name { t_tys } ->
           Global.set_smooth
             (Modules.find_value (Lident.Name(Ident.source name))) t_tys)
         env;
       (* output the signature *)
       if !Misc.print_smoothness_types
       then
         Env.iter
           (fun name { t_tys } ->
             Psmooth.declaration ff (Ident.source name) t_tys) env
  with
  | Error(loc, kind) -> message loc kind
                          
(* the main entry function *)
let program ff ({ p_impl_list } as p) =
  (* add the type for polymorphic primitives (+.,*.,...) from Stdlib *)
  add_type_for_polymorphic_primitives_in_stdlib ();
  (* type check the sequence of declarations *)
  List.iter (implementation ff) p_impl_list;
  p
