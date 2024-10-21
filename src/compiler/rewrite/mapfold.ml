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

(* generic mapfold iterator on the Zelus AST *)
(* it is based on a technique used in the Heptagon compiler (2012) *)
(* The text below is borrowed from the Heptagon compiler *)
(* https://gitlab.inria.fr/synchrone/heptagon *)

(* The basic idea is to provide a top-down pass over an Heptagon AST. If you
   call [program_it hept_funs_default acc p], with [p] an heptagon program and
   [acc] the accumulator of your choice, it will go through the whole AST,
   passing the accumulator without touching it, and applying the identity
   function on the AST. It'll return [p, acc].

   To customize your pass, you need to redefine some functions of the
   [hept_funs_default] record. Each field in the record handles one node type,
   and the function held in the field will be called when the iterator
   encounters the corresponding node type.

   You can imitate the default functions defined here, and named corresponding
   to the [hep_it_funs] field (corresponding to the Zelus AST type).  There
   are two types of functions, the ones handling record types, and the more
   special ones handling sum types. If you don't want to deal with every
   constructor, you can simply finish your matching with [| _ -> raise
   Misc.Fallback]: it will then fall back to the generic handling for these
   construtors, defined in this file.

   Note that the iterator is a top-down one. If you want to use it in a
   bottom-up manner (e.g. visiting expressions before visiting an equation), you
   need to manually call the proper recursive function (defined here) in the
   beginning of your handler. For example:

   [
   let eq funs acc eq =
     let (eq, acc) = Mapfold.eq funs acc eq in
     ...
     (eq, acc)
   ]

   The record provided here and the functions to iterate over any type
   ([type_it]) enable lots of different ways to deal with the AST.

   Discover it by yourself !*)

(* /!\ Do not EVER put in your funs record one of the generic iterator function
   [type_it]. You should always put a custom version or the default version
   provided in this file. Trespassers will loop infinitely! /!\ *)

open Misc
open Error
open Zelus
open Defnames

(* preliminary version *)

exception Fallback

let stop funs _ _ = raise Fallback

type ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs =
  {
    intro_ident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Ident.t -> Ident.t * 'a;
    build :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> 'ienv1 Ident.Env.t -> 'ienv2 Ident.Env.t * 'a;
    lident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Lident.t -> Lident.t * 'a;
    var_ident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Ident.t -> Ident.t * 'a;
    state_ident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Ident.t -> Ident.t * 'a;
    last_ident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> last -> last * 'a;
    init_ident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Ident.t -> Ident.t * 'a;
    emit_ident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Ident.t -> Ident.t * 'a;
    der_ident :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Ident.t -> Ident.t * 'a;
    typevar :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> name -> name * 'a;
    typeconstr :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> Lident.t -> Lident.t * 'a;
    type_expression :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> type_expression -> type_expression * 'a;
    typedecl :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> ((name * name list * type_decl) as 'ty) -> 'ty * 'a;
    constr_decl :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> constr_decl -> constr_decl * 'a;
    kind :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> kind -> kind * 'a;
    interface :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a -> interface -> interface * 'a;
    size_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs ->
      'a ->
      size_expression -> size_expression * 'a;
  }

type ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs =
  {
    global_funs :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) global_it_funs;
    pattern :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> 'info1 pattern -> 'info2 pattern * 'a;
    write_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> defnames -> defnames * 'a;
    leq_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) leq -> ('info2, 'ienv2) leq * 'a;
    slet_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) leq list -> ('info2, 'ienv2) leq list * 'a;
    equation :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) eq -> ('info2, 'ienv2) eq * 'a;
    scondpat :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) scondpat -> ('info2, 'ienv2) scondpat * 'a;
    expression :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) exp -> ('info2, 'ienv2) exp * 'a;
    vardec :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, ('info1, 'ienv1) exp) vardec ->
      ('info2, ('info2, 'ienv2) exp) vardec * 'a;
    for_vardec :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1) for_vardec -> ('info2, 'ienv2) for_vardec * 'a;
    for_out_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1) for_out -> ('info2, 'ienv2) for_out * 'a;
    for_returns :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1) for_returns -> ('info2, 'ienv2) for_returns * 'a;
    for_exp_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1) for_exp -> ('info2, 'ienv2) for_exp * 'a;
    for_eq_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1) for_eq -> ('info2, 'ienv2) for_eq * 'a;
    block :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1, ('info1, 'ienv1) exp, ('info1, 'ienv1) eq) block ->
      ('info2, 'ienv2, ('info2, 'ienv2) exp, ('info2, 'ienv2) eq) block * 'a;
    result :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) result -> ('info2, 'ienv2) result * 'a;
    funexp :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) funexp -> ('info2, 'ienv2) funexp * 'a;
    match_handler_eq :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('ienv1, 'info1 pattern, ('info1, 'ienv1) eq) match_handler
      -> ('ienv2, 'info2 pattern, ('info2, 'ienv2) eq) match_handler * 'a; 
    match_handler_e :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a
      -> ('ienv1, 'info1 pattern, ('info1, 'ienv1) exp) match_handler
      -> ('ienv2, 'info2 pattern, ('info2, 'ienv2) exp) match_handler * 'a;
    if_eq :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) eq * ('info1, 'ienv1) eq ->
      (('info2, 'ienv2) eq * ('info2, 'ienv2) eq) * 'a; 
    reset_eq :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) eq -> ('info2, 'ienv2) eq * 'a; 
    reset_e :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ('info1, 'ienv1) exp -> ('info2, 'ienv2) exp * 'a; 
    present_handler_eq :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a 
      -> ('ienv1, ('info1, 'ienv1) scondpat,
          ('info1, 'ienv1) eq) present_handler 
      -> ('ienv2, ('info2, 'ienv2) scondpat,
          ('info2, 'ienv2) eq) present_handler
         * 'a; 
    present_handler_e :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a 
      -> ('ienv1, ('info1, 'ienv1) scondpat, ('info1, 'ienv1) exp)
           present_handler 
      -> ('ienv2, ('info2, 'ienv2) scondpat, ('info2, 'ienv2) exp)
           present_handler * 'a; 
    automaton_handler : 
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a 
      -> ('info1, 'ienv1,
          ('info1, 'ienv1, ('info1, 'ienv1) exp, ('info1, 'ienv1) eq) block)
           automaton_handler 
      -> ('info2, 'ienv2,
          ('info2, 'ienv2, ('info2, 'ienv2) exp, ('info2, 'ienv2) eq) block)
           automaton_handler * 'a;
    letdecl :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> ((name * Ident.t) list * ('info1, 'ienv1) leq)
      -> ((name * Ident.t) list * ('info2, 'ienv2) leq) * 'a;
    implementation :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1) implementation -> ('info2, 'ienv2) implementation * 'a;
    program :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a ->
      ('info1, 'ienv1) program -> ('info2, 'ienv2) program * 'a;
    get_index :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> Ident.num -> Ident.num * 'a;
    set_index :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs ->
      'a -> Ident.num -> Ident.num * 'a;
    open_t :
      ('a, 'info1, 'ienv1, 'info2, 'ienv2) it_funs -> 'a -> name -> name * 'a;
  }

(* introduce a fresh name *)
let intro_ident_it global_funs acc ident =
  global_funs.intro_ident global_funs acc ident

and intro_ident global_funs acc ident = ident, acc

(* global ident *)
let lident_it global_funs acc lident = global_funs.lident global_funs acc lident

and lident global_funs acc lident = lident, acc

(* Build from an environment *)
let build_it global_funs acc env = global_funs.build global_funs acc env

and build global_funs acc env = env, acc

and last_ident_it global_funs acc l = global_funs.last_ident global_funs acc l

and last_ident global_funs acc { copy; id } =
  let id, acc = global_funs.var_ident global_funs acc id in
  { copy; id }, acc

and init_ident_it global_funs acc id = global_funs.init_ident global_funs acc id

and init_ident global_funs acc id = 
  global_funs.var_ident global_funs acc id

and emit_ident_it global_funs acc id = global_funs.emit_ident global_funs acc id

and emit_ident global_funs acc id = 
  global_funs.var_ident global_funs acc id

and der_ident_it global_funs acc id = global_funs.der_ident global_funs acc id

and der_ident global_funs acc id = 
  global_funs.var_ident global_funs acc id

let rec pattern_it funs acc pat =
  try funs.pattern funs acc pat
  with Fallback -> pattern funs acc pat

and pattern funs acc ({ pat_desc } as p) =
  let pat_desc, acc = match pat_desc with
    | Ewildpat | Econstpat _ -> pat_desc, acc
    | Econstr0pat(lname) ->
       let lname, acc = lident_it funs.global_funs acc lname in
       Econstr0pat(lname), acc
    | Evarpat(v) ->
       let v, acc = var_ident_it funs.global_funs acc v in
       Evarpat(v), acc
    | Etuplepat(p_list) ->
       let p_list, acc = Util.mapfold (pattern_it funs) acc p_list in
       Etuplepat(p_list), acc
    | Econstr1pat(lname, p_list) ->
       let lname, acc = lident_it funs.global_funs acc lname in
       let p_list, acc = Util.mapfold (pattern_it funs) acc p_list in
       Econstr1pat(lname, p_list), acc
    | Erecordpat(n_p_list) ->
       let n_p_list, acc =
         Util.mapfold 
           (fun acc { label; arg } ->
             let label, acc = lident_it funs.global_funs acc label in
             let p, acc = pattern_it funs acc p in
             { label; arg = p}, acc) acc n_p_list in
       Erecordpat(n_p_list), acc
    | Ealiaspat(p1, n) ->
       let p1, acc = pattern_it funs acc p1 in
       let n, acc = var_ident_it funs.global_funs acc n in
       Ealiaspat(p1, n), acc
    | Eorpat(p1, p2) ->
       let p1, acc = pattern_it funs acc p1 in
       let p2, acc = pattern_it funs acc p2 in
       Eorpat(p1, p2), acc
    | Etypeconstraintpat(p1, ty) ->
       let p1, acc = pattern_it funs acc p1 in
       let ty, acc = type_expression_it funs.global_funs acc ty in
       Etypeconstraintpat(p1, ty), acc in
  { p with pat_desc }, acc

and var_ident_it global_funs acc x =
  global_funs.var_ident global_funs acc x

and var_ident global_funs acc x = x, acc

and state_ident_it global_funs acc x =
  global_funs.state_ident global_funs acc x

and state_ident global_funs acc x = x, acc

and typevar_it global_funs acc x =
  global_funs.typevar global_funs acc x

and typevar global_funs acc x = x, acc

and typeconstr_it global_funs acc x =
  global_funs.typeconstr global_funs acc x

and typeconstr global_funs acc x = x, acc

and kind_it global_funs acc k =
  global_funs.kind global_funs acc k

and kind global_funs acc k = k, acc

and type_expression_it global_funs acc ty =
  try global_funs.type_expression global_funs acc ty
  with Fallback -> type_expression global_funs acc ty

and type_expression global_funs acc ({ desc } as ty) =
  let desc, acc = match desc with
  | Etypevar(name) ->
     let name, acc = typevar_it global_funs acc name in
     Etypevar(name), acc
  | Etypeconstr(lname, ty_list) ->
     let lname, acc = typeconstr_it global_funs acc lname in
     let ty_list, acc =
       Util.mapfold (type_expression_it global_funs) acc ty_list in
     Etypeconstr(lname, ty_list), acc 
  | Etypetuple(ty_list) ->
     let ty_list, acc =
       Util.mapfold (type_expression_it global_funs) acc ty_list in
     Etypetuple(ty_list), acc     
  | Etypefun { ty_kind; ty_name_opt; ty_arg; ty_res } ->
     let ty_kind, acc = kind_it global_funs acc ty_kind in
     let ty_name_opt, acc =
       Util.optional_with_map (intro_ident_it global_funs) acc ty_name_opt in
     let ty1, acc = type_expression_it global_funs acc ty_arg in
     let ty2, acc = type_expression_it global_funs acc ty_res in
     Etypefun { ty_kind; ty_name_opt; ty_arg; ty_res }, acc
  | Etypevec(ty, si) ->
    let ty, acc = type_expression_it global_funs acc ty in
    let si, acc = size_it global_funs acc si in
    Etypevec(ty, si), acc in
  { ty with desc }, acc

and size_it global_funs acc si =
  try global_funs.size_t global_funs acc si
  with Fallback -> size_t global_funs acc si

and size_t global_funs acc ({ desc } as si) =
  let desc, acc = match desc with
  | Size_int _ -> desc, acc
  | Size_frac { num; denom } ->
     let num, acc = size_it global_funs acc num in
     Size_frac { num; denom }, acc
  | Size_var(id) ->
     let id, acc = var_ident_it global_funs acc id in
     Size_var(id), acc
  | Size_op(op, si1, si2) ->
     let si1, acc = size_it global_funs acc si1 in
     let si2, acc = size_it global_funs acc si2 in
     Size_op(op, si1, si2), acc in
  { si with desc }, acc

let write_it funs acc w = funs.write_t funs acc w

and write_t funs acc { dv; di; der } =
  let rename n = let m, _ = var_ident_it funs.global_funs acc n in m in
  let dv = Ident.S.map rename dv in
  let di = Ident.S.map rename di in
  let der = Ident.S.map rename der in
  { dv; di; der }, acc

let default_t f acc d =
  match d with
  | Init(e) -> let e, acc = f acc e in Init(e), acc
  | Else(e) -> let e, acc = f acc e in Else(e), acc
  | NoDefault -> NoDefault, acc

let rec for_exit_t funs acc ({ for_exit } as fe) =
  let for_exit, acc = expression_it funs acc for_exit in
  { fe with for_exit }, acc

and for_kind_t funs acc for_kind =
  match for_kind with
  | Kforeach -> Kforeach, acc
  | Kforward(for_exit_opt) ->
     let for_exit_opt, acc = 
       Util.optional_with_map (for_exit_t funs) acc for_exit_opt in
     Kforward(for_exit_opt), acc

and for_size_t funs acc e = expression_it funs acc e

and for_input_t funs acc ({ desc } as fi) =
  let desc, acc = match desc with
    | Einput {id; e; by } ->
       let id, acc = var_ident_it funs.global_funs acc id in
       let e, acc = expression_it funs acc e in
       let by, acc = Util.optional_with_map (expression_it funs) acc by in
       Einput { id; e; by }, acc
    | Eindex ({ id; e_left; e_right } as ind) ->
       let id, acc = var_ident_it funs.global_funs acc id in
       let e_left, acc = expression_it funs acc e_left in
       let e_right, acc = expression_it funs acc e_right in
       Eindex { ind with id; e_left; e_right }, acc in
  { fi with desc }, acc

and for_exp_it funs acc for_body = funs.for_exp_t funs acc for_body

and for_exp_t funs acc for_body =
  match for_body with
  | Forexp { exp; default } ->
     let exp, acc = expression_it funs acc exp in
     let default, acc =
       Util.optional_with_map (expression_it funs) acc default in
     Forexp { exp; default }, acc
  | Forreturns(f) ->
     let f, acc = for_returns_it funs acc f in
     Forreturns f, acc

and for_eq_it funs acc for_body = funs.for_eq_t funs acc for_body

and for_eq_t funs acc { for_out; for_block; for_out_env } =
  (* names in [for_out_env] are local to the for_block *)
  let for_out_env, acc =
    build_it funs.global_funs acc for_out_env in
  let for_out, acc =
    Util.mapfold (for_out_it funs) acc for_out in
  let for_block, acc = block_it funs acc for_block in
  { for_out; for_block; for_out_env }, acc

and slet_it funs acc leq_list = funs.slet_t funs acc leq_list

and slet_t funs acc leq_list = Util.mapfold (leq_it funs) acc leq_list

and leq_it funs acc leq = funs.leq_t funs acc leq

and leq_t funs acc ({ l_eq; l_env } as leq) =
  let l_env, acc = build_it funs.global_funs acc l_env in
  let l_eq, acc = equation_it funs acc l_eq in
  { leq with l_eq; l_env }, acc

and scondpat_it funs acc scpat =
  try funs.scondpat funs acc scpat
  with Fallback -> scondpat funs acc scpat

and scondpat funs acc ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     let scpat1, acc = scondpat_it funs acc scpat1 in
     let scpat2, acc = scondpat_it funs acc scpat2 in
     { scpat with desc = Econdand(scpat1, scpat2) }, acc
  | Econdor(scpat1, scpat2) ->
     let scpat1, acc = scondpat_it funs acc scpat1 in
     let scpat2, acc = scondpat_it funs acc scpat2 in
     { scpat with desc = Econdor(scpat1, scpat2) }, acc
  | Econdexp(e) ->
     let e, acc = expression_it funs acc e in
     { scpat with desc = Econdexp(e) }, acc
  | Econdpat(e, p) ->
     let e, acc = expression_it funs acc e in
     let p, acc = pattern_it funs acc p in
     { scpat with desc = Econdpat(e, p) }, acc
  | Econdon(scpat, e) ->
     let scpat, acc = scondpat_it funs acc scpat in
     let e, acc = expression_it funs acc e in
     { scpat with desc = Econdon(scpat, e) }, acc

and vardec_it funs acc v = funs.vardec funs acc v

and vardec funs acc
({ var_name; var_default; var_init; var_typeconstraint } as v) =
  let var_name, acc =
    var_ident_it funs.global_funs acc var_name in
  let var_default, acc =
    Util.optional_with_map (expression_it funs) acc var_default in
  let var_init, acc =
    Util.optional_with_map (expression_it funs) acc var_init in
  let var_typeconstraint, acc =
    Util.optional_with_map
      (type_expression_it funs.global_funs) acc var_typeconstraint in
  { v with var_name; var_default; var_init; var_typeconstraint }, acc

and for_vardec_it funs acc v = funs.for_vardec funs acc v

and for_vardec funs acc ({ desc = { for_array; for_vardec } } as f) =
  let for_vardec, acc = vardec_it funs acc for_vardec in
  { f with desc = { for_array; for_vardec } }, acc

and for_out_it funs acc v = funs.for_out_t funs acc v

and for_out_t funs acc
  ({ desc = { for_name; for_out_name; for_init; for_default } } as f) =
  let for_name, acc = var_ident_it funs.global_funs acc for_name in
  let for_out_name, acc = 
    Util.optional_with_map
      (var_ident_it funs.global_funs) acc for_out_name in
  let for_init, acc =
    Util.optional_with_map (expression_it funs) acc for_init in
  let for_default, acc =
    Util.optional_with_map (expression_it funs) acc for_default in
  { f with desc = { for_name; for_out_name; for_init; for_default } },
  acc         
     
and for_returns_it funs acc f = funs.for_returns funs acc f

and for_returns funs acc { r_returns; r_block; r_env } =
  let r_env, acc = build_it funs.global_funs acc r_env in
  let r_returns, acc =
    Util.mapfold (for_vardec_it funs) acc r_returns in
  let r_block, acc = block_it funs acc r_block in
  { r_returns; r_block; r_env }, acc

and block_it funs acc b = funs.block funs acc b

and block funs acc ({ b_vars; b_body; b_write; b_env } as b) =
  let b_env, acc = build_it funs.global_funs acc b_env in
  let b_vars, acc = 
    Util.mapfold (vardec_it funs) acc b_vars in
  let b_body, acc = equation_it funs acc b_body in
  let b_write, acc = write_t funs acc b_write in
  { b with b_vars; b_body; b_env; b_write }, acc

and result_it funs acc r =
  try funs.result funs acc r
  with Fallback -> result funs acc r

and result funs acc ({ r_desc } as r) =
  let r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc = expression_it funs acc e in Exp(e), acc
    | Returns(b_eq) ->
       let b_eq, acc = block_it funs acc b_eq in Returns(b_eq), acc in
  { r with r_desc }, acc

and funexp_it funs acc f = funs.funexp funs acc f

and funexp funs acc ({ f_args; f_body; f_env } as f) =
  let arg acc v_list = Util.mapfold (vardec_it funs) acc v_list in
  let f_env, acc = build_it funs.global_funs acc f_env in
  let f_args, acc = Util.mapfold arg acc f_args in
  let f_body, acc = result_it funs acc f_body in
  { f with f_args; f_body; f_env }, acc

(* Expressions *)
and expression_it funs acc e =
  try funs.expression funs acc e
  with Fallback -> expression funs acc e

and expression funs acc ({ e_desc; e_loc } as e) =
  match e_desc with
  | Econst _ -> e, acc
  | Econstr0 { lname } ->
     let lname, acc = lident_it funs.global_funs acc lname in
     { e with e_desc = Econstr0 { lname } }, acc
  | Eglobal { lname } ->
     let lname, acc = lident_it funs.global_funs acc lname in
     { e with e_desc = Eglobal { lname } }, acc
  | Evar(x) ->
     let x, acc = var_ident_it funs.global_funs acc x in
     { e with e_desc = Evar(x) }, acc
  | Elast(l) ->
     let l, acc = last_ident_it funs.global_funs acc l in
     { e with e_desc = Elast(l) }, acc
  | Etuple(e_list) ->
     let e_list, acc = Util.mapfold (expression_it funs) acc e_list in
     { e with e_desc = Etuple(e_list) }, acc
  | Econstr1 { lname; arg_list } ->
     let lname, acc = lident_it funs.global_funs acc lname in
     let arg_list, acc = Util.mapfold (expression_it funs) acc arg_list in
     { e with e_desc = Econstr1 { lname; arg_list } }, acc
  | Erecord(l_e_list) -> 
     let l_e_list, acc =
       Util.mapfold (fun acc { label; arg } ->
           let label, acc = lident_it funs.global_funs acc label in
           let arg, acc = expression_it funs acc arg in 
           { label; arg }, acc) acc l_e_list in
     { e with e_desc = Erecord(l_e_list) }, acc
  | Erecord_access { label; arg } ->
     let label, acc = lident_it funs.global_funs acc label in
     let arg, acc = expression_it funs acc arg in
     { e with e_desc = Erecord_access { label; arg } }, acc
  | Erecord_with(e_record, l_e_list) -> 
     let e_record, acc = expression_it funs acc e_record in
     let l_e_list, acc =
       Util.mapfold
	 (fun acc { label; arg } ->
           let label, acc = lident_it funs.global_funs acc label in
           let arg, acc = expression_it funs acc e in { label; arg }, acc)
         acc l_e_list in
     { e with e_desc = Erecord_with(e_record, l_e_list) }, acc
  | Eapp ({ f; arg_list } as a) ->
     let arg_list, acc = Util.mapfold (expression_it funs) acc arg_list in
     let f, acc = expression_it funs acc f in
     { e with e_desc = Eapp { a with f; arg_list } }, acc
  | Eop(op, e_list) ->
     let e_list, acc = Util.mapfold (expression_it funs) acc e_list in
     { e with e_desc = Eop(op, e_list) }, acc
  | Etypeconstraint(e_ty, ty) ->
     let e_ty, acc = expression_it funs acc e_ty in
     let ty, acc = type_expression_it funs.global_funs acc ty in
     { e with e_desc = Etypeconstraint(e_ty, ty) }, acc
  | Elet(l, e_let) ->
     let l, acc = leq_it funs acc l in
     let e_let, acc = expression_it funs acc e_let in
     { e with e_desc = Elet(l, e_let) }, acc
  | Elocal(eq_b, e) ->
     let eq_b, acc = block_it funs acc eq_b in
     let e, acc = expression_it funs acc e in
     { e with e_desc = Elocal(eq_b, e) }, acc
  | Epresent({ handlers; default_opt }) ->
     let handlers, acc =
       Util.mapfold (present_handler_e_it funs) acc handlers in
     let default_opt, acc = default_t (expression_it funs) acc default_opt in
     { e with e_desc = Epresent { handlers; default_opt } }, acc 
  | Ematch({ e; handlers } as m) ->
     let e, acc = expression_it funs acc e in
     let handlers, acc =
       Util.mapfold (match_handler_e_it funs) acc handlers in
     { e with e_desc = Ematch { m with e; handlers } }, acc
  | Eassert e -> let e, acc = expression_it funs acc e in
                 { e with e_desc = Eassert(e) }, acc
  | Ereset(e_body, e_c) ->
     let e_body, acc = reset_e_it funs acc e_body in
     let e_c, acc = expression_it funs acc e_c in
     { e with e_desc = Ereset(e_body, e_c) }, acc
  | Esizeapp { f; size_list } -> 
     let size_list, acc = 
       Util.mapfold (size_it funs.global_funs) acc size_list in
     let v, acc = expression_it funs acc f in
     { e with e_desc = Esizeapp { f; size_list } }, acc
  | Efun f ->
     let f, acc = funexp_it funs acc f in
     { e with e_desc = Efun f }, acc
  | Eforloop
     ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
     let for_env, acc = build_it funs.global_funs acc for_env in
     let for_index, acc =
       Util.optional_with_map (var_ident_it funs.global_funs) acc for_index in
     let for_size, acc =
       Util.optional_with_map (for_size_t funs) acc for_size in
     let for_input, acc =
       Util.mapfold (for_input_t funs) acc for_input in
     let for_body, acc = for_exp_it funs acc for_body in
     (* the exit condition can depend on output variables of the loop *)
     let for_kind, acc = for_kind_t funs acc for_kind in
     { e with e_desc =
                Eforloop
                  { f with for_size; for_kind; for_index; for_input;
                           for_body; for_env } }, acc

(* match handler - equations and expressions *)
and match_handler_eq_it funs acc m_handler =
  funs.match_handler_eq funs acc m_handler

and match_handler_eq funs acc ({ m_pat; m_body; m_env } as m_h) =
  let m_env, acc = build_it funs.global_funs acc m_env in
  let m_pat, acc = pattern_it funs acc m_pat in
  let m_body, acc = equation_it funs acc m_body in
  { m_h with m_pat; m_body; m_env }, acc

and if_eq_it funs acc (eq_true, eq_false) =
  funs.if_eq funs acc (eq_true, eq_false)

and if_eq funs acc (eq_true, eq_false) =
  let eq_true, acc = equation_it funs acc eq_true in
  let eq_false, acc = equation_it funs acc eq_false in
  (eq_true, eq_false), acc

and reset_eq_it funs acc eq = funs.reset_eq funs acc eq

and reset_eq funs acc eq = equation_it funs acc eq

and reset_e_it funs acc eq = funs.reset_e funs acc eq

and reset_e funs acc e = expression_it funs acc e

and match_handler_e_it funs acc m_handler =
  funs.match_handler_e funs acc m_handler

and match_handler_e funs acc ({ m_pat; m_body; m_env } as m_h) =
  let m_env, acc = build_it funs.global_funs acc m_env in
  let m_pat, acc = pattern_it funs acc m_pat in
  let m_body, acc = expression_it funs acc m_body in
  { m_h with m_pat; m_body; m_env }, acc

and present_handler_eq_it funs acc p_handler =
  funs.present_handler_eq funs acc p_handler

and present_handler_eq funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_env, acc = build_it funs.global_funs acc p_env in
  let p_cond, acc = scondpat_it funs acc p_cond in
  let p_body, acc = equation_it funs acc p_body in
  { p_b with p_cond; p_body; p_env }, acc

and present_handler_e_it funs acc p_handler =
  funs.present_handler_e funs acc p_handler

and present_handler_e funs acc ({ p_cond; p_body; p_env } as p_b) =
  let p_env, acc = build_it funs.global_funs acc p_env in
  let p_cond, acc = scondpat_it funs acc p_cond in
  let p_body, acc = expression_it funs acc p_body in
  { p_b with p_cond; p_body }, acc

(* Equations *)
and equation_it funs acc eq =
    try funs.equation funs acc eq
  with Fallback -> equation funs acc eq

and equation funs acc ({ eq_desc; eq_write; eq_loc } as eq) = 
  let eq, acc = match eq_desc with
    | EQeq(p, e) ->
       let p, acc = pattern_it funs acc p in
       let e, acc = expression_it funs acc e in
       { eq with eq_desc = EQeq(p, e) }, acc
    | EQinit(x, e) ->
       let x, acc = init_ident_it funs.global_funs acc x in
       let e, acc = expression_it funs acc e in
       { eq with eq_desc = EQinit(x, e) }, acc
    | EQemit(x, e_opt) ->
       let x, acc = emit_ident_it funs.global_funs acc x in
       let e_opt, acc =
         Util.optional_with_map (expression_it funs) acc e_opt in
       { eq with eq_desc = EQemit(x, e_opt) }, acc
    | EQder { id; e; e_opt; handlers } ->
       let body acc ({ p_cond; p_body; p_env } as p_b) =
         let p_env, acc = build_it funs.global_funs acc p_env in
         let p_cond, acc = scondpat_it funs acc p_cond in
         let p_body, acc = expression_it funs acc p_body in
         { p_b with p_cond; p_body }, acc in
       let id, acc = der_ident_it funs.global_funs acc id in
       let e, acc = expression_it funs acc e in
       let e_opt, acc =
         Util.optional_with_map (expression_it funs) acc e_opt in
       let handlers, acc = Util.mapfold body acc handlers in
       { eq with eq_desc = EQder { id; e; e_opt; handlers } }, acc
    | EQif { e; eq_true; eq_false } ->
       let e, acc = expression_it funs acc e in
       let (eq_true, eq_false), acc =
         if_eq_it funs acc (eq_true, eq_false) in
       { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
    | EQmatch({ e; handlers } as m) ->
       let e, acc = expression_it funs acc e in
       let handlers, acc =
         Util.mapfold (match_handler_eq_it funs) acc handlers in
       { eq with eq_desc = EQmatch { m with e; handlers } }, acc
    | EQlocal(eq_b) ->
       let eq_b, acc = block_it funs acc eq_b in
       { eq with eq_desc = EQlocal(eq_b) }, acc
    | EQand({ eq_list } as a) ->
       let eq_list, acc = Util.mapfold (equation_it funs) acc eq_list in
       { eq with eq_desc = EQand { a with eq_list } }, acc
    | EQpresent({ handlers; default_opt }) ->
       let handlers, acc = 
         Util.mapfold (present_handler_eq_it funs) acc handlers in
       let default_opt, acc = default_t (equation_it funs) acc default_opt in
       { eq with eq_desc = EQpresent { handlers; default_opt } }, acc
    | EQautomaton({ handlers; state_opt } as a) ->
       let state_opt, acc = Util.optional_with_map (state funs) acc state_opt in
       let handlers, acc = 
         Util.mapfold (automaton_handler_it funs) acc handlers in
       { eq with eq_desc = EQautomaton({ a with handlers; state_opt }) }, acc
    | EQempty -> eq, acc
    | EQassert(e) ->
       let e, acc = expression_it funs acc e in
       { eq with eq_desc = EQassert(e) }, acc
    | EQforloop
       ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
      let for_env, acc = build_it funs.global_funs acc for_env in
       let for_index, acc =
         Util.optional_with_map (var_ident_it funs.global_funs) acc for_index in
       let for_size, acc =
         Util.optional_with_map (for_size_t funs) acc for_size in
       let for_input, acc =
         Util.mapfold (for_input_t funs) acc for_input in
       let for_body, acc = for_eq_it funs acc for_body in
       (* the exit condition can depend on output variables of the loop *)
       let for_kind, acc = for_kind_t funs acc for_kind in
       { eq with eq_desc =
                   EQforloop
                     { f with for_size; for_kind; for_index; for_input;
                              for_body; for_env } }, acc
    | EQreset(eq, e_c) ->
       let eq, acc = reset_eq_it funs acc eq in
       let e_c, acc = expression_it funs acc e_c in
       { eq with eq_desc = EQreset(eq, e_c) }, acc
    | EQlet(leq, eq) ->
       let leq, acc = leq_it funs acc leq in
       let eq, acc = equation_it funs acc eq in
       { eq with eq_desc = EQlet(leq, eq) }, acc
    | EQsizefun({ sf_id; sf_id_list; sf_e; sf_env } as sf) ->
       let sf_env, acc = build_it funs.global_funs acc sf_env in
       let sf_id, acc = var_ident_it funs.global_funs acc sf_id in
       let sf_id_list, acc =
         Util.mapfold (var_ident_it funs.global_funs) acc sf_id_list in
       let sf_e, acc = expression_it funs acc sf_e in
       { eq with eq_desc =
                   EQsizefun { sf with sf_id; sf_id_list; sf_e; sf_env } },
       acc in
  let eq_write, acc = write_t funs acc eq_write in
  { eq with eq_write }, acc

(* automata *)
and statepat funs acc ({ desc } as spat) =
  let desc, acc = match desc with
    | Estate0pat(id) ->
       let id, acc = state_ident_it funs.global_funs acc id in
       Estate0pat(id), acc
    | Estate1pat(id, id_list) ->
       let id, ac = state_ident_it funs.global_funs acc id in
       let id_list, acc =
         Util.mapfold (var_ident_it funs.global_funs)
           acc id_list in
       Estate1pat(id, id_list), acc in
  { spat with desc }, acc

and state funs acc ({ desc } as st) =
  let desc, acc  = match desc with
    | Estate0(id) ->
       let id, acc = state_ident_it funs.global_funs acc id in
       Estate0(id), acc
    | Estate1(id, e_list) ->
       let id, acc =  state_ident_it funs.global_funs acc id in
       let e_list, acc =
         Util.mapfold (expression_it funs) acc e_list in
       Estate1(id, e_list), acc
    | Estateif(e, st1, st2) ->
       let e, acc = expression_it funs acc e in
       let st1, acc = state funs acc st1 in
       let st2, acc = state funs acc st2 in
       Estateif(e, st1, st2), acc in
  { st with desc }, acc

and escape funs acc ({ e_cond; e_let; e_body; e_next_state; e_env } as esc) =
  let e_env, acc = build_it funs.global_funs acc e_env in
  let e_cond, acc = scondpat_it funs acc e_cond in
  let e_let, acc = slet_it funs acc e_let in
  let e_body, acc = block_it funs acc e_body in
  let e_next_state, acc = state funs acc e_next_state in
  { esc with e_cond; e_let; e_body; e_next_state; e_env }, acc

and automaton_handler_it funs acc handler =
  funs.automaton_handler funs acc handler

and automaton_handler funs acc ({ s_state; s_let; s_body; s_trans; s_env } as h) =
  let s_env, acc = build_it funs.global_funs acc s_env in
  let s_state, acc = statepat funs acc s_state in
  let s_let, acc = slet_it funs acc s_let in
  let s_body, acc = block_it funs acc s_body in
  let s_trans, acc = Util.mapfold (escape funs) acc s_trans in
  { h with s_state; s_let; s_body; s_trans; s_env }, acc

let typedecl_it funs acc ty_decl = funs.typedecl funs acc ty_decl

and typedecl funs acc ty_decl = ty_decl, acc

let open_it funs acc name = funs.open_t funs acc name

let open_t funs acc name = name, acc

let letdecl_it funs acc (d_names, d_leq) =
  funs.letdecl funs acc (d_names, d_leq)

and letdecl funs acc (d_names, d_leq) =
  let d_leq, acc = leq_it funs acc d_leq in
  let d_names, acc =
    Util.mapfold
      (fun acc (name, id) ->
        let id, acc =
          var_ident_it funs.global_funs acc id in (name, id), acc)
      acc d_names in
  (d_names, d_leq), acc

let rec implementation_it funs acc impl =
  try funs.implementation funs acc impl
  with Fallback -> implementation funs acc impl

and implementation funs acc ({ desc } as impl) =
  let desc, acc = match desc with
    | Eopen(name) ->
       let name, acc = open_it funs acc name in
       Eopen(name), acc
    | Eletdecl { d_names; d_leq } ->
       let (d_names, d_leq), acc = letdecl_it funs acc (d_names, d_leq) in
       Eletdecl { d_names; d_leq }, acc
    | Etypedecl { name; ty_params; ty_decl } ->
       let (name, ty_params, ty_decl), acc =
         typedecl_it
           funs.global_funs acc (name, ty_params, ty_decl) in
       Etypedecl { name; ty_params; ty_decl }, acc in
  { impl with desc }, acc

let constr_decl_it global_funs acc c_decl =
  global_funs.constr_decl global_funs acc c_decl

and constr_decl global_funs acc ({ desc } as c_decl) =
  let desc, acc = match desc with
  | Econstr0decl _ -> desc, acc
  | Econstr1decl(name, ty_list) ->
     let ty_list, acc =
       Util.mapfold (type_expression_it global_funs) acc ty_list in
     Econstr1decl(name, ty_list), acc in
  { c_decl with desc }, acc

let typedecl_it global_funs acc (name, ty_params, ty_decl) =
  global_funs.typedecl global_funs acc (name, ty_params, ty_decl)

and typedecl global_funs acc (name, ty_params, ty_decl) =
  let one_ty_decl acc ({ desc } as ty_decl) =
    let desc, acc = match desc with
      | Eabstract_type -> Eabstract_type, acc
      | Eabbrev(ty_e) ->
         let ty_e, acc = type_expression_it global_funs acc ty_e in
         Eabbrev(ty_e), acc
      | Evariant_type(constr_list) ->
         let constr_list, acc =
           Util.mapfold (constr_decl_it global_funs) acc constr_list in
         Evariant_type(constr_list), acc
      | Erecord_type(name_ty_list) ->
         let name_ty_list, acc =
           Util.mapfold
             (fun acc (name, ty) ->
               let ty, acc = type_expression_it global_funs acc ty in
               (name, ty), acc) acc name_ty_list in
         Erecord_type(name_ty_list), acc in
    { ty_decl with desc }, acc in
  let ty_decl, acc = one_ty_decl acc ty_decl in
  (name, ty_params, ty_decl), acc

let set_index_it funs acc n = funs.set_index funs acc n

and set_index funs acc n = n, acc

let get_index_it funs acc n = funs.get_index funs acc n

and get_index funs acc n = n, acc

let program_it funs acc p = funs.program funs acc p

and program funs acc { p_impl_list; p_index } =
  let n, acc = set_index_it funs acc p_index in
  let p_impl_list, acc = 
    Util.mapfold (implementation_it funs) acc p_impl_list in
  let p_index, acc = get_index_it funs acc n in
  { p_impl_list; p_index }, acc  

let interface_it global_funs acc interf =
  global_funs.interface global_funs acc interf

and interface global_funs acc interf = interf, acc

let default_global_funs =
  { build;
    intro_ident;
    lident;
    var_ident;
    state_ident;
    last_ident;
    init_ident;
    emit_ident;
    der_ident;
    typevar;
    typeconstr;
    kind;
    type_expression;
    typedecl;
    constr_decl;
    interface;
    size_t;
  }

let defaults =
  { global_funs = default_global_funs;
    pattern;
    write_t;
    leq_t;
    slet_t;
    equation;
    scondpat;
    expression;
    vardec;
    for_vardec;
    for_out_t;
    for_returns;
    for_exp_t;
    for_eq_t;
    block;
    result;
    funexp;
    match_handler_eq;
    match_handler_e;
    if_eq;
    reset_eq;
    reset_e;
    automaton_handler;
    present_handler_eq;
    present_handler_e;
    letdecl;
    implementation;
    program;
    get_index;
    set_index;
    open_t;
  }


let default_global_stop =
  { build = stop;
    lident = stop;
    intro_ident = stop;
    var_ident = stop;
    state_ident = stop;
    last_ident = stop;
    init_ident = stop;
    emit_ident = stop;
    der_ident = stop;
    typevar = stop;
    typeconstr = stop;
    kind = stop;
    type_expression = stop;
    typedecl = stop;
    constr_decl = stop;
    interface = stop;
    size_t = stop;
  }


let defaults_stop =
  { global_funs = default_global_stop;
    pattern = stop;
    write_t = stop;
    leq_t = stop;
    slet_t = stop;
    equation = stop;
    scondpat = stop;
    expression = stop;
    vardec = stop;
    for_vardec = stop;
    for_out_t = stop;
    for_returns = stop;
    for_exp_t = stop;
    for_eq_t = stop;
    block = stop;
    result = stop;
    funexp = stop;
    match_handler_eq = stop;
    match_handler_e = stop;
    if_eq = stop;
    reset_eq = stop;
    reset_e = stop;
    automaton_handler = stop;
    present_handler_eq = stop;
    present_handler_e = stop;
    letdecl = stop;
    implementation = stop;
    program = stop;
    get_index = stop;
    set_index = stop;
    open_t = stop;
  }

