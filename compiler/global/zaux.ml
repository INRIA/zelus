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
(* Functions to build expressions *)

open Location
open Initial
open Deftypes
open Zelus
open Ident
open Lident


let desc e = e.desc
let make x = { desc = x; loc = no_location }

let emake desc ty =
  { e_desc = desc; e_loc = no_location; e_typ = ty; e_caus = [] }
let pmake desc ty =
  { p_desc = desc; p_loc = no_location; p_typ = ty; p_caus = [] }
let eqmake desc =
  { eq_desc = desc; eq_loc = no_location; eq_write = Deftypes.empty }

let evoid = emake (Econst(Evoid)) typ_unit
let efalse = emake (Econst(Ebool(false))) typ_bool
let etrue = emake (Econst(Ebool(true))) typ_bool
let truepat = pmake (Econstpat(Ebool(true))) typ_bool
let wildpat = pmake (Ewildpat) Deftypes.no_typ
let zero = emake (Econst(Efloat(0.0))) Initial.typ_float
let infinity = 
  emake (Eglobal(Modname(Initial.pervasives_name "infinity"))) typ_float
let tproduct ty_list = Deftypes.make (Tproduct(ty_list))
let tuplepat pat_list = 
  let ty_list = List.map (fun { p_typ = ty } -> ty) pat_list in
  pmake (Etuplepat(pat_list)) (tproduct ty_list)
let tuple e_list = 
  let ty_list = List.map (fun { e_typ = ty } -> ty) e_list in
  emake (Etuple(e_list)) (tproduct ty_list)

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

let binop op e1 e2 ty =
  emake (Eapp(Eop(false, Modname(Initial.pervasives_name op)), [e1;e2])) ty
let plus e1 e2 = binop "+." e1 e2 Initial.typ_float
let minus e1 e2 = binop "-." e1 e2 Initial.typ_float
let diff e1 e2 = binop "<>" e1 e2 Initial.typ_float
let or_op e1 e2 = binop "||" e1 e2 Initial.typ_bool
let on_op e1 e2 = binop "on" e1 e2 Initial.typ_zero
let min_op e1 e2 = binop "min" e1 e2 Initial.typ_float
let greater_or_equal e1 e2 = binop ">=" e1 e2 Initial.typ_bool
let up e = emake (Eapp(Eup, [e])) Initial.typ_zero
		 
let pre e = emake (Eapp(Eunarypre, [e])) e.e_typ
let minusgreater e1 e2 = emake (Eapp(Eminusgreater, [e1;e2])) e1.e_typ
let fby e1 e2 = emake (Eapp(Efby, [e1;e2])) e1.e_typ

let ifthenelse e1 e2 e3 = emake (Eapp(Eifthenelse, [e1;e2;e3])) e2.e_typ
let after_list e n_list = emake (Eapp(Eafter(n_list), [e])) e.e_typ
let after e n = after_list e [n]

let make_local env eq_list = 
  { l_eq = eq_list; l_env = env; l_loc = Location.no_location }
let make_let env eq_list e =
  match eq_list with
  | [] -> e | _ -> emake (Elet(make_local env eq_list, e)) e.e_typ

let make_block env eq_list =
  { b_vars = []; b_locals = []; b_body = eq_list; b_loc = Location.no_location;
    b_env = env; b_write = Deftypes.empty }

let eq_make n e = eqmake (EQeq(varpat n e.e_typ, e))
let eq_next n e = eqmake (EQnext(n, e, None))
let eq_init n e = eqmake (EQinit(n, e))
let pluseq_make n e = eqmake (EQpluseq(n, e))
  
let eq_reset eq_list e = eqmake (EQreset(eq_list, e))
let eq_match e l = eqmake (EQmatch(ref true, e, l))
let eq_block b = eqmake (EQblock(b))
let eq_der x e = eqmake (EQder(x, e, None, []))

let init i eq_list = (eq_init i etrue) :: (eq_make i efalse) :: eq_list
 
let vardec i =
  { vardec_name = i; vardec_default = None;
    vardec_combine = None; vardec_loc = no_location }

let vardec_from_entry i { t_sort = sort } =
  let d_opt, c_opt =
    match sort with
      | Sval -> None, None
      | Svar { v_default = None; v_combine = c_opt }
      | Smem { m_init = (None | Some(None)); m_combine = c_opt } -> None, c_opt
      | Svar { v_default = Some(c); v_combine = c_opt } -> Some(Default(c)), c_opt
      | Smem { m_init = Some(Some(c)); m_combine = c_opt } ->
	Some(Init(c)), c_opt in
  { vardec_name = i; vardec_default = d_opt;
    vardec_combine = c_opt; vardec_loc = no_location }
    
      
