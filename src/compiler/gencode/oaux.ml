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

(* auxiliary functions *)

open Obc
       
(* the list of methods *)
let step = "step" (* computes values and possible changes of states *)
let reset = "reset" (* resets the discrete state *)
let copy = "copy" (* copy the discrete state *)
let derivative = "derivative" (* computes the values of derivatives *)
let crossing = "crossing" (* computes the zero-crossing functions *)
let horizon = "horizon"  (* compute the next time horizon *)

(* auxiliary functions *)
let letin p e1 i2 = Elet(p, e1, i2)
let letvar id ty e1 e2 = Eletvar { id; is_mutable = false;
                                   ty; e_opt = Some(e1); e = e2 }
let bool v = Econst(Ebool(v))
let int_const v = Econst(Eint(v))
let float_const v = Econst(Efloat(v))
let operator op = Eglobal { lname = Modname (Initial.stdlib_name op) }
let binop op e1 e2 = Eapp { f = operator op; arg_list = [e1; e2] }
let plus e1 e2 = binop "+" e1 e2
let mult e1 e2 = binop "*" e1 e2
let minus e1 e2 = binop "-" e1 e2
let min e1 e2 = binop "min" e1 e2
let zero = int_const 0
let one = int_const 1
let ffalse = bool false
let void = Econst(Evoid)
let is_zero e = match e with Econst(Eint(0)) -> true | _ -> false
let plus_opt e1 e2 =
  match e1, e2 with
  | Econst(Eint(0)), _ -> e2
  | _, Econst(Eint(0)) -> e1
  | Econst(Eint(v1)), Econst(Eint(v2)) -> Econst(Eint(v1 + v2))
  | _ -> plus e1 e2
let minus_opt e1 e2 =
  match e1, e2 with
  | _, Econst(Eint(0)) -> e1
  | Econst(Eint(v1)), Econst(Eint(v2)) -> Econst(Eint(v1 - v2))
  | _ -> minus e1 e2
let mult_opt e1 e2 =
  match e1, e2 with
  | Econst(Eint(1)), _ -> e2
  | _, Econst(Eint(1)) -> e1
  | Econst(Eint(v1)), Econst(Eint(v2)) -> Econst(Eint(v1 * v2))
  | _ -> mult e1 e2

let var is_mutable id = Evar { is_mutable; id }
let global lname = Eglobal { lname }
let varmut x = var true x

let ifthenelse c e1 e2 = Eifthenelse(c, e1, e2)

let sequence e_list =
  let seq e e_list =
    match e, e_list with
    | Econst(Evoid), _ -> e_list
    | _, [] -> [e]
    | _ -> e :: e_list in
  let e_list = List.fold_right seq e_list [] in
  match e_list with
  | [] -> Econst(Evoid)
  | _ -> Esequence e_list
                   
let rec left_state_access lv e_list =
  match e_list with
  | [] -> lv
  | e :: e_list -> left_state_access (Eleft_state_index(lv, e)) e_list
