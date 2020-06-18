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

(* Functions to build expressions *)

open Misc
open Location
open Initial
open Deftypes
open Zelus
open Ident
open Lident


let desc e = e.desc
let make x = { desc = x; loc = no_location }

let prime_app = { app_inline = false; app_statefull = false }
	    
let emake desc ty =
  { e_desc = desc; e_loc = no_location;
    e_typ = ty; e_caus = Defcaus.no_typ; e_init = Definit.no_typ }
let pmake desc ty =
  { p_desc = desc; p_loc = no_location;
    p_typ = ty; p_caus = Defcaus.no_typ; p_init = Definit.no_typ }
let eqmake desc =
  { eq_desc = desc; eq_loc = no_location; eq_write = Deftypes.empty;
    eq_safe = false; eq_index = -1 }

let global lname =
  Eglobal { lname = lname; typ_instance = Deftypes.no_typ_instance }

let const c ty = emake (Econst c) ty
let constr0 ln ty = emake (Econstr0 ln) ty
let evoid = const Evoid typ_unit
let efalse = const (Ebool(false)) typ_bool
let etrue = const (Ebool(true)) typ_bool
let truepat = pmake (Econstpat(Ebool(true))) typ_bool
let falsepat = pmake (Econstpat(Ebool(false))) typ_bool
let wildpat = pmake (Ewildpat) Deftypes.no_typ
let zero = emake (Econst(Efloat(0.0))) Initial.typ_float
let one = emake (Econst(Efloat(1.0))) Initial.typ_float
let minus_one = emake (Econst(Efloat(-1.0))) Initial.typ_float
let infinity = 
  emake (global (Modname(Initial.stdlib_name "infinity"))) typ_float
let tproduct ty_list = Deftypes.make (Tproduct(ty_list))
let tuplepat pat_list = 
  let ty_list = List.map (fun { p_typ = ty } -> ty) pat_list in
  pmake (Etuplepat(pat_list)) (tproduct ty_list)
let tuple e_list = 
  let ty_list = List.map (fun { e_typ = ty } -> ty) e_list in
  emake (Etuple(e_list)) (tproduct ty_list)
let record l_list e_list ty =
  emake (Erecord(List.map2 (fun l e -> (l, e)) l_list e_list)) ty
    
let rec orpat pat_list =
  match pat_list with
    | [] -> assert false
    | [pat] -> pat
    | pat :: pat_list -> pmake (Eorpat(pat, orpat pat_list)) pat.p_typ

let varpat name ty = pmake (Evarpat(name)) ty
let var name ty = emake (Elocal(name)) ty

let pair e1 e2 =  emake (Etuple([e1; e2])) (tproduct [e1.e_typ; e2.e_typ])
let pairpat p1 p2 = pmake (Etuplepat([p1; p2])) (tproduct [p1.p_typ; p2.p_typ])

let patalias p n ty = pmake (Ealiaspat(p, n)) ty
let last x ty = emake (Elast(x)) ty
let float v = emake (Econst(Efloat(v))) Initial.typ_float
let bool v = emake (Econst(Ebool(v))) Initial.typ_bool

let float_varpat x = varpat x Initial.typ_float
let bool_varpat x = varpat x Initial.typ_bool
let float_var x = var x Initial.typ_float
let bool_var x = var x Initial.typ_bool

let float_last x = last x Initial.typ_float
let bool_last x = last x Initial.typ_bool

let global_in_stdlib lname ty =
  emake (global (Modname(Initial.stdlib_name lname))) ty

let maketype ty_arg_list ty_res =
  let make ty = { t_desc = ty; t_level = generic; t_index = symbol#name } in
  make (Tfun(Tany, None, make (Tproduct(ty_arg_list)), ty_res))

let rec funtype ty_arg_list ty_res =
  let make ty = { t_desc = ty; t_level = generic; t_index = symbol#name } in
  match ty_arg_list with
  | [] -> ty_res
  | ty_arg :: ty_arg_list ->
      make (Tfun(Tany, None, ty_arg, funtype ty_arg_list ty_res))

let unop op e ty =
  emake (Eapp(prime_app,
	      global_in_stdlib op (maketype [e.e_typ] ty), [e])) ty
let binop op e1 e2 ty =
  emake (Eapp(prime_app,
	      global_in_stdlib op (maketype [e1.e_typ; e2.e_typ] ty),
	      [e1;e2])) ty

let plus e1 e2 = binop "+." e1 e2 Initial.typ_float
let minus e1 e2 = binop "-." e1 e2 Initial.typ_float
let diff e1 e2 = binop "<>" e1 e2 Initial.typ_bool
let or_op e1 e2 = binop "||" e1 e2 Initial.typ_bool
let and_op e1 e2 = binop "&&" e1 e2 Initial.typ_bool
let on_op e1 e2 = binop "on" e1 e2 Initial.typ_zero
let min_op e1 e2 = binop "min" e1 e2 Initial.typ_float
let greater_or_equal e1 e2 = binop ">=" e1 e2 Initial.typ_bool
let greater e1 e2 = binop ">" e1 e2 Initial.typ_bool
let up e = emake (Eop(Eup, [e])) Initial.typ_zero
let pre e = emake (Eop(Eunarypre, [e])) e.e_typ
let minusgreater e1 e2 = emake (Eop(Eminusgreater, [e1;e2])) e1.e_typ
let fby e1 e2 = emake (Eop(Efby, [e1;e2])) e1.e_typ
let ifthenelse e1 e2 e3 =
  emake (Eop(Eifthenelse, [e1;e2;e3])) e2.e_typ
let sgn e =
  ifthenelse (greater e zero) one minus_one
let record_access e l ty = emake (Erecord_access(e, l)) ty
    
let extend_local env eq_list ({ l_eq = l_eq_list; l_env = l_env } as l) = 
  { l with l_eq = eq_list @ l_eq_list; l_env = Env.append env l_env }
let make_local env eq_list = 
  extend_local env eq_list
    { l_rec = true; l_eq = [];
      l_env = Env.empty; l_loc = Location.no_location }
let make_let env eq_list e =
  match eq_list with
  | [] -> e | _ -> emake (Elet(make_local env eq_list, e)) e.e_typ

let vardec i =
  { vardec_name = i; vardec_default = None;
    vardec_combine = None; vardec_loc = no_location }

let vardec_from_entry i { t_sort = sort } =
  let d_opt, c_opt =
    match sort with
      | Sstatic -> None, None
      | Sval -> None, None
      | Svar { v_default = None; v_combine = c_opt }
      | Smem { m_init = (Noinit | InitEq); m_combine = c_opt } ->
	 None, c_opt
      | Smem { m_init = InitDecl(c); m_combine = c_opt } ->
	 Some(Init(c)), c_opt
      | Svar { v_default = Some(c); v_combine = c_opt } ->
         Some(Default(c)), c_opt in
  { vardec_name = i; vardec_default = d_opt;
    vardec_combine = c_opt; vardec_loc = no_location }

let extend_block env eq_list
    ({ b_vars = b_vars; b_env = b_env; b_body = body_eq_list } as b) =
  let b_vars =
    Env.fold (fun i entry acc -> vardec_from_entry i entry :: acc)
             env b_vars in
  { b with b_vars = b_vars; b_body = eq_list @ body_eq_list;
    b_env = Env.append env b_env }

let make_block env eq_list =
  extend_block env eq_list
    { b_vars = []; b_env = Env.empty; b_locals = [];
      b_body = []; b_loc = Location.no_location; b_write = Deftypes.empty }

let eq_make n e = eqmake (EQeq(varpat n e.e_typ, e))
let eq_next n e = eqmake (EQnext(n, e, None))
let eq_init n e = eqmake (EQinit(n, e))
let pluseq_make n e = eqmake (EQpluseq(n, e))
  
let eq_reset eq_list e = eqmake (EQreset(eq_list, e))
let eq_match e l = eqmake (EQmatch(ref true, e, l))
let eq_block b = eqmake (EQblock(b))
let eq_der x e = eqmake (EQder(x, e, None, []))


let handler p b =
  { m_pat = p; m_body = b; m_env = Env.empty;
    m_reset = false; m_zero = false }

let eq_ifthenelse e b1 b2 =
  eq_match e [handler truepat b1; handler falsepat b2]

let eq_ifthen e b = eqmake (EQmatch(ref false, e, [handler truepat b]))
    
let before eq_list =
  match eq_list with
  | [] -> assert false
  | [eq] -> eq
  | _ -> eqmake (EQbefore(eq_list))
let par eq_list =
  match eq_list with
  | [] -> assert false
  | [eq] -> eq
  | _ -> eqmake (EQand(eq_list))
		
let init i eq_list = (eq_init i etrue) :: (eq_make i efalse) :: eq_list

(* find the major step in the current environment *)
(* If it already exist in the environment *)
(* returns it. Otherwise, create one *)
let new_major env =
  let m = Ident.fresh "major" in
  let env =
    Env.add m { t_sort = Deftypes.major (); t_typ = Initial.typ_bool } env in
  let major = var m Initial.typ_bool in
  env, major
	 
let major env =
  let exception Return of Zelus.exp in
  let find x t =
    match t with
    | { t_sort = Smem { m_kind = Some(Major) }; t_typ = typ } ->
       raise (Return(var x typ))
    | _ -> () in
  try
    Env.iter find env;
    new_major env
  with
  | Return(x) -> env, x 

