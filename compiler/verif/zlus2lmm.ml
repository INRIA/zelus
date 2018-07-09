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

(* Translation into Lustre-- *)

(* no automaton, no present, no pre/fby/->. All names must be *)
(* pair-wise differents *)

(* Tr(ck)(res)(match e with
               | p1 -> E1 | ... | pn -> En) =

   with one defined variable y (defnames = {y}) and used variable x
   (example: E1 = local t in do t = x + 3 and y = t + 2 done)

becomes:

   local c in
   do
     c = Tr(ck)(e)
   and
     Tr(c on c1)(E1)[y_1/y]
   and
     ...
   and
     Tr(c on cn)(En)[y_n/y]
   and
     c1 = test(p1)(c) and ... and cn = test(pn)(c)
   and
     pat(p1) = c and ... and pat(pn) = c
   and
     y = if c1 then y_1 else ... if cn then y_n [else pre y]

where:

  test(p)(c) returns an expression testing that the pattern p matches c
  pat(p) returns a pattern with variables only

Tr(ck)(x = e) = x = if ck then Tr(ck)(e) else pre x
                with the special case that if base then e else e' = e

*)

open Location
open Misc
open Ident
open Deftypes
open Zelus
open Lmm
open List
open Format

type error =
  | Ehybrid_operator
  | Earray_operator
  | Eapplication

exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin match kind with
  | Ehybrid_operator ->
     eprintf "@[%aTranslation to L--: Hybrid operators are not treated.@.@]"
             output_location loc
  | Earray_operator ->
     eprintf "@[%aTranslation to L--: Array operators are not treated.@.@]"
             output_location loc
  | Eapplication ->
     eprintf "@[%aTranslation to L--: \
                  Application must be of the form f(e1,...,en).@.@]"
             output_location loc
  end

(* The translation function takes and returns a set *)
(* of equations, assertions and environment *)
type return =
    { eqs: eq State.t;
      env: tentry Env.t State.t;
      assertion: exp State.t }

let empty =
  { eqs = State.empty; env = State.empty; assertion = State.empty  }

let with_env ({ env = env0 } as return) env =
  { return with env = State.cons env env0 }

let with_eq ({ eqs = eqs } as return) eq =
  { return with eqs = State.cons eq eqs }

let par { eqs = eqs1; env = env1; assertion = as1 }
        { eqs = eqs2; env = env2; assertion = as2 } =
  { eqs = State.par eqs1 eqs2; env = State.par env1 env2;
    assertion = State.par as1 as2 }

let eq_make k x e ck =
  { eq_kind = k; eq_ident = x;
    eq_exp = e; eq_clock = ck }

let e_true = Lconst(Lbool(true))
let e_false = Lconst(Lbool(false))

let bool_op op e1 e2 =
  Lapp(Lop(Lident.Modname(Initial.pervasives_name op)),[e1; e2])

let equal_op e1 e2 = bool_op "=" e1 e2
let and_op e1 e2 =
  if e1 = e_true then e2
  else if e2 = e_true then e1
  else bool_op "&" e1 e2
let or_op e1 e2 =
  if e1 = e_false then e2
  else if e2 = e_false then e1
  else bool_op "or" e1 e2
let rec or_list e_list =
  match e_list with
  | [] -> e_true
  | [e] -> e
  | e :: l -> or_op e (or_list l)
let ifthenelse e1 e2 e3 =
  Lapp(Lifthenelse, [e1; e2; e3])
let unarypre x = Lapp(Lunarypre, [Llocal(x)])

let on ck c = Ck_on(ck, Llocal(c))
let relse res c = Res_else(res, c)

(* from a clock to a boolean expression *)
let rec clock = function
  | Ck_base -> e_true
  | Ck_on(Ck_base, e) -> e
  | Ck_on(ck, e) -> and_op (clock ck) e

(* from a reset to a boolean expression *)
let rec reset = function
  | Res_never -> e_false
  | Res_else(Res_never, e) -> e
  | Res_else(res, e) -> or_op (reset res) e

(* immediate values *)
let immediate = function
  | Eint(i) -> Lint(i)
  | Efloat(f) -> Lfloat(f)
  | Ebool(b) -> Lbool(b)
  | Echar(c) -> Lchar(c)
  | Estring(s) -> Lstring(s)
  | Evoid -> Lvoid

(* Translation of a type. For the moment, only a small set of *)
(* basic types are translated *)
let rec type_of { t_desc = ty } =
  match ty with
  | Deftypes.Tconstr(q, [], _) ->
     if q = Initial.int_ident then Tint
     else if q = Initial.int32_ident then Tint
     else if q = Initial.int64_ident then Tint
     else if q = Initial.bool_ident then Tbool
     else if q = Initial.zero_ident then Tbool
     else if q = Initial.float_ident then Tfloat
     else if q = Initial.char_ident then Tchar
     else if q = Initial.string_ident then Tstring
     else if q = Initial.unit_ident then Tunit
     else Lmm.Tconstr(q)
  | Tconstr _ -> assert false
  | Tvar | Tproduct _ | Tvec _ | Tfun _ -> assert false
  | Tlink(ty) -> type_of ty

let type_expression ty_e =
  let { typ_body = ty } = Interface.scheme_of_type ty_e in
  type_of ty

let env_of_env env =
  Env.map (fun { Deftypes.t_typ = ty } -> { t_typ = type_of ty }) env

(* translate an operator *)
let operator loc op e_list =
  match op with
  | Eifthenelse -> Lapp(Lifthenelse, e_list)
  | Eunarypre -> Lapp(Lunarypre, e_list)
  | Eminusgreater -> Lapp(Lminusgreater, e_list)
  | Efby -> Lapp(Lfby, e_list)
  | Eup | Einitial | Edisc
  | Ehorizon -> error loc Ehybrid_operator
  | Eaccess | Eupdate | Econcat | Eslice _ -> error loc Earray_operator
  | Etest -> assert false

(* renaming of a name by an other *)
let rename x subst =
  try Env.find x subst
  with | Not_found -> x (* assert false *)

(* the set of shared variables from a set of defined names *)
let shared_variables { dv = dv } = dv

(* returns the expression associated to [x] in a substitution [name_to_exp] *)
(* if [x] is unbound, returns [last x] *)
let get x name_to_exp =
  try
    Env.find x name_to_exp
  with
  | Not_found -> Llast(x)

(* translate expressions *)
let rec expression ck { e_desc = desc; e_loc = loc } =
  match desc with
  | Elocal(id) -> Llocal(id)
  | Eglobal { lname = lid } -> Lglobal(lid)
  | Econst(im) -> Lconst(immediate im)
  | Econstr0(lid) -> Lconstr0(lid)
  | Elast(x) -> Llast(x)
  | Eapp(_, { e_desc = Eglobal { lname = lid } }, e_list) ->
     Lapp(Lop(lid), List.map (expression ck) e_list)
  | Eapp _ -> error loc Eapplication
  | Eop(op, e_list) ->
     operator loc op (map (expression ck) e_list)
  | Erecord_access(e, lid) ->
     Lrecord_access(expression ck e, lid)
  | Erecord(l_e_list) ->
     Lrecord
       (map (fun (l, e) -> (l, expression ck e)) l_e_list)
  | Etypeconstraint(e, _) -> expression ck e
  | Ematch(total, exp, match_handler_list) -> assert false
  | Etuple(e_list) -> assert false
  | Elet(loc, e) -> assert false
  | Eseq(e1, e2) -> assert false
  | Eperiod(period) -> assert false
  | Eblock(blocks, e) -> assert false
  | Epresent(h_list, o_e) -> assert false


(* [split s_set ({ eqs } as return) = name_to_exp, return'] splits eqs into *)
(* two complementary sets of equations *)
(* [name_to_exp] associates an expression to any names from [s_set] *)
let split s_set ({ eqs = eqs } as return) =
  let eq_name_exp, eqs =
    State.partition (fun { eq_ident = id } -> S.mem id s_set) eqs in
  let name_to_exp =
    State.fold (fun { eq_ident = id; eq_exp = e } acc -> Env.add id e acc)
               eq_name_exp Env.empty in
  name_to_exp, { return with eqs = eqs }

(* for a pair [pat, e] computes the equation [pat_v = e] and boolean *)
(* condition c where [pat_v] is only made of variables and [c] *)
(* is true when [pat] matches [e] *)
let rec filter { p_desc = p_desc } e =
  match p_desc with
  | Ewildpat -> e_true, empty
  | Evarpat(id) ->
     e_true, { empty with eqs = State.singleton (eq_make Def id e Ck_base) }
  | Econstpat(c) -> equal_op (Lconst(immediate c)) e, empty
  | Econstr0pat(c) -> equal_op (Lconstr0(c)) e, empty
  | Etuplepat(p_list) ->
     (* introduce n fresh names *)
     let n_ty_list =
       map (fun { p_typ = ty } -> Ident.fresh "", type_of ty) p_list in
     let e_list = map (fun (n, _) -> Llocal(n)) n_ty_list in
     let env =
       List.fold_left
         (fun env (n, ty) ->
           Env.add n { t_typ = ty } env) Env.empty n_ty_list in
     let cond, return = filter_list p_list e_list in
     cond, with_env return env
  | Ealiaspat(p, id) ->
     let cond, return = filter p e in
     cond, with_eq return (eq_make Def id e Ck_base)
  | Etypeconstraintpat(p, _) -> filter p e
  | Eorpat(p1, p2) ->
     let cond1, return1 = filter p1 e in
     let cond2, return2 = filter p2 e in
     or_op cond1 cond2, par return1 return2
  | Erecordpat(l_p_list) ->
     let cond, return =
       fold_left
	 (fun (cond, return) (l, p) ->
	  let cond_l_p, return_l_p = filter p (Lrecord_access(e, l)) in
	  and_op cond cond_l_p, par return return_l_p)
         (e_true, empty) l_p_list in
     cond, return

and filter_list p_list e_list =
  fold_left2
    (fun (cond, return) p e ->
      let cond_p_e, return_p_e = filter p e in
      and_op cond cond_p_e, par return return_p_e) (e_true, empty)
    p_list e_list

(* [equation ck res eq = return] *)
let rec equation ck res { eq_desc = desc; eq_write = defnames } =
  match desc with
  | EQeq({ p_desc = Evarpat(x) }, e) ->
     with_eq empty (eq_make Def x (expression ck e) ck)
  | EQinit(x, e) ->
     let e = expression ck e in
     with_eq empty (eq_make (Init(res)) x e ck)
  | EQreset(eq_list, e) ->
     let e = expression ck e in
     equation_list ck (relse res e) eq_list
  | EQmatch(total, e, p_h_list) ->
     (* first translate [e] *)
     let e = expression ck e in
     (* then compute the set of shared variables *)
     let s_set = shared_variables defnames in
     (* introduce [n] fresh clock names [c1,..., cn] *)
     let c_list = map (fun _ -> Ident.fresh "") p_h_list in

     (* translate the list of body *)
     let equations_from_handler c { m_body = b } =
       let return = block (on ck c) res b in
       let name_to_exp, return = split s_set return in
       name_to_exp, return in

     let cond_name_to_exp_list, return =
       fold_right2
	 (fun c p_h (cond_name_to_exp_list, return) ->
	  let name_to_exp, return_name_to_exp = equations_from_handler c p_h in
	  (c, name_to_exp) :: cond_name_to_exp_list,
          par return return_name_to_exp)
	 c_list p_h_list ([], empty) in

     (* translate the list of patterns *)
     let patterns_from_handler return c { m_pat = p } =
       let cond, return_cond = filter p e in
       (* Need some thinking to find the correct kind and clock. *)
       with_eq (par return return_cond) (eq_make Def c cond ck) in
     let return_cond =
       fold_left2 patterns_from_handler empty c_list p_h_list in

     (* the variables [c1,...,cn] cannot be true at the same time *)
     let assertion = or_list (map (fun c -> Llocal(c)) c_list) in
     let env = List.fold_left
                 (fun acc c -> Env.add c { t_typ = Tbool } acc)
                 Env.empty c_list in

     (* merge results for every shared variable. Returns *)
     (* if c1 then e1 else ... en *)
     let rec merge x cond_name_to_exp_list =
       match cond_name_to_exp_list with
       | [] -> assert false
       | [cond, name_to_exp] -> get x name_to_exp
       | (cond, name_to_exp) :: cond_name_to_exp_list ->
	  Lapp(Lifthenelse,
		   [Llocal(cond); get x name_to_exp;
		    merge x cond_name_to_exp_list]) in
     let eqs =
       S.fold
	 (fun x eqs ->
	  State.cons (eq_make Def x (merge x cond_name_to_exp_list) ck) eqs)
	 s_set State.empty in
     par return (par return_cond
                     { eqs = eqs; env = State.singleton env;
                       assertion = State.singleton assertion })
  | EQeq _ | EQnext _ | EQblock _ | EQemit _ | EQautomaton _
  | EQpresent _ | EQder _ | EQpluseq _
  | EQand _| EQbefore _| EQforall _-> assert false

and equation_list ck res eq_list =
  fold_left (fun acc eq -> par acc (equation ck res eq)) empty eq_list

and block ck res { b_body = body_eq_list; b_env = n_env } =
  let return = equation_list ck res body_eq_list in
  with_env return (env_of_env n_env)

let local ck res { l_eq = eq_list; l_env = l_env } =
  let return = equation_list ck res eq_list in
  with_env return (env_of_env l_env)

(* translate a top level expression *)
let let_expression ck res n_output ({ e_desc = desc } as e) =
  match desc with
  | Elet(l, e) ->
     let return = local ck res l in
     let e = expression ck e in
     with_eq return (eq_make Def n_output e ck)
  | _ ->
     let e = expression ck e in
     with_eq empty (eq_make Def n_output e ck)

let kind = function | S | AS | A | AD -> A | D -> D | C -> assert false

(* translation of a type declaration *)
let typedecl n params td =
  let decl td =
    match td with
    | Eabstract_type -> Labstract_type
    | Evariant_type(n_list) -> Lvariant_type(n_list)
    | Erecord_type(n_ty_list) ->
       Lrecord_type
	 (List.map (fun (n, ty) -> (n, type_expression ty)) n_ty_list)
    | Eabbrev _ -> assert false in
  match params with
  | [] -> Ltypedecl(n, decl td)
  | _ -> assert false

let implementation lmm_nodes lmm_list impl =
  match impl.desc with
  | Eopen _ -> lmm_list
  | Etypedecl(n, params, td) ->
     typedecl n params td :: lmm_list
  | Econstdecl(n, _, e) ->
      if Misc.S.mem n lmm_nodes
      then Lconstdecl(n, expression Ck_base e) :: lmm_list
     else lmm_list
  | Efundecl(n, { f_kind = k; f_args = p_list; f_env = f_env; f_body = e }) ->
     if Misc.S.mem n lmm_nodes then
       let iset = List.fold_left (Vars.fv_pat S.empty) S.empty p_list in
       let i_list = S.elements iset in
       let n_output = Ident.fresh "out" in
       let { eqs = eqs; env = env; assertion = assertion } =
	 let_expression Ck_base Res_never n_output e in
       let env =
	 State.fold
    (fun env acc -> Env.append env acc) env (env_of_env f_env) in
       let eq_list =
	 State.fold (fun eq acc -> eq :: acc) eqs [] in
       let assertion =
	 State.fold (fun e acc -> e :: acc) assertion [] in
       Lfundecl(n, { f_inputs = i_list;
		     f_output = n_output;
		     f_env = env;
		     f_body = eq_list;
		     f_assert = assertion }) :: lmm_list
     else lmm_list

let implementation_list lmm_nodes impl_list =
  rev (fold_left (implementation lmm_nodes) [] impl_list)
    
