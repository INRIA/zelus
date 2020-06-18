(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Translation into Lmm. This is applied after complex pattern matchings *)
(* have been turned into primitive pattern matchings on an enumerated *)
(* set of values (in particular booleans) *)

(* no automaton, no present, no pre/fby/->. All names must be *)
(* pair-wise differents; no complex pattern matchings *)

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
  | Etype
  | Ehybrid_operator
  | Earray_operator
  | Eapplication

exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin match kind with
  | Etype ->
     eprintf "@[%aTranslation to L--: This type cannot be translated.@.@]"
             output_location loc
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

let on ck ln c = Ck_on(ck, ln, c)
let relse res c = Res_else(res, c)

(* immediate values *)
let immediate = function
  | Eint(i) -> Lint(i)
  | Efloat(f) -> Lfloat(f)
  | Ebool(b) -> Lbool(b)
  | Echar(c) -> Lchar(c)
  | Estring(s) -> Lstring(s)
  | Evoid -> Lvoid

(** Translation of a pattern. *)
(* It must be either a constructor or a boolean value. Otherwise, *)
(* the translation fails. *)
let constr0pat { p_desc = p_desc } =
  match p_desc with
  | Econstpat(Ebool(b)) -> Lboolpat(b)
  | Econstr0pat(c) -> Lconstr0pat(c)
  | _ -> assert false

(* Translation of a type. For the moment, only a small set of *)
(* basic types are translated *)
let rec type_of loc { t_desc = ty } =
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
  | Tconstr _ -> error loc Etype
  | Tproduct(ty_list) -> Lmm.Tproduct(List.map (type_of loc) ty_list)
  | Tvar | Tvec _ | Tfun _ -> error loc Etype
  | Tlink(ty) -> type_of loc ty

let type_expression loc ty_e =
  let { typ_body = ty } = Interface.scheme_of_type ty_e in
  type_of loc ty

let env_of_env loc env =
  Env.map (fun { Deftypes.t_typ = ty } -> { t_typ = type_of loc ty }) env

(* translate an operator *)
let operator loc op e_list =
  match op with
  | Eifthenelse -> Lapp(Lifthenelse, e_list)
  | Eunarypre -> Lapp(Lunarypre, e_list)
  | Eminusgreater -> Lapp(Lminusgreater, e_list)
  | Efby -> Lapp(Lfby, e_list)
  | Eup | Einitial | Edisc | Ehorizon -> error loc Ehybrid_operator
  | Eaccess | Eupdate | Econcat | Eslice _ -> error loc Earray_operator
  | Etest | Eatomic -> assert false

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
  | Econstr1 _ -> assert false
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
  | Etuple(e_list) -> Ltuple(List.map (expression ck) e_list)
  | Ematch _ | Eseq _ | Elet _
  | Eperiod _ | Eblock _ | Epresent _ -> assert false


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
     (* the conditional is necessary of the form:
      *- match e with P1 -> B1 | ... | Pn -> Bn
      *- with P1 | ... | Pn are the element of a sum type *)
     (* first translate [e] *)
     let e = expression ck e in
     (* then compute the set of shared variables *)
     let s_set = shared_variables defnames in

     (* translate the list of handlers *)
     let equations_from_handler e p b =
       let co = constr0pat p in
       let return = block (on ck co e) res b in
       let name_to_exp, return = split s_set return in
       co, name_to_exp, return in

     let constrpat_to_exp_list, return =
       Misc.map_fold
         (fun return { m_pat = p; m_body = b } ->
            let co, name_to_exp, return_name_to_exp =
              equations_from_handler e p b in
	    (co, name_to_exp), par return return_name_to_exp)
	 empty p_h_list in

     (* merge results for every shared variable. Returns *)
     (* merge x (P1 -> e1) ... (Pn -> en) *)
     let merge e x constrpat_name_to_exp_list =
       let p_e_list =
         List.map
           (fun (co, name_to_exp) -> co, get x name_to_exp)
           constrpat_name_to_exp_list in
       Lmerge(e, p_e_list) in
     let eq_list =
       S.fold
	 (fun x eq_list ->
           (eq_make Def x (merge e x constrpat_to_exp_list) ck) :: eq_list)
         s_set [] in
     List.fold_left with_eq empty eq_list
  | EQeq _ | EQnext _ | EQblock _ | EQemit _ | EQautomaton _
  | EQpresent _ | EQder _ | EQpluseq _
  | EQand _| EQbefore _| EQforall _-> assert false

and equation_list ck res eq_list =
  fold_left (fun acc eq -> par acc (equation ck res eq)) empty eq_list

and block ck res { b_body = body_eq_list; b_env = n_env; b_loc = loc } =
  let return = equation_list ck res body_eq_list in
  with_env return (env_of_env loc n_env)

let local ck res { l_eq = eq_list; l_env = l_env; l_loc = loc } =
  let return = equation_list ck res eq_list in
  with_env return (env_of_env loc l_env)

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
let typedecl loc n params td =
  let decl { desc = desc } =
    match desc with
    | Eabstract_type -> Labstract_type
    | Evariant_type _ -> assert false
    | Erecord_type(n_ty_list) ->
       Lrecord_type
	 (List.map (fun (n, ty) -> (n, type_expression loc ty)) n_ty_list)
    | Eabbrev _ -> assert false in
  match params with
  | [] -> Ltypedecl(n, decl td)
  | _ -> assert false

let implementation lmm_nodes lmm_list impl =
  match impl.desc with
  | Eopen _ -> lmm_list
  | Etypedecl(n, params, td) ->
     typedecl impl.loc n params td :: lmm_list
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
          (fun env acc -> Env.append env acc) env (env_of_env impl.loc f_env) in
       let eq_list = State.list [] eqs in
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
    
