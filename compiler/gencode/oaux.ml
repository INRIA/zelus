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
let letin p e1 i2 = Olet(p, e1, i2)
let letvar x ty e1 i2 = Oletvar(x, false, ty, Some(e1), i2)
let bool v = Oconst(Obool(v))
let int_const v = Oconst(Oint(v))
let float_const v = Oconst(Ofloat(v))
let operator op = Oglobal(Modname (Initial.stdlib_name op))
let plus e1 e2 = Oapp(operator "+", [e1; e2])
let mult e1 e2 = Oapp(operator "*", [e1; e2])
let minus e1 e2 = Oapp(operator "-", [e1; e2])
let min e1 e2 = Oapp(operator "min", [e1; e2])
let zero = int_const 0
let one = int_const 1
let ffalse = bool false
let void = Oconst(Ovoid)
let is_zero e = match e with Oconst(Oint(0)) -> true | _ -> false
let plus_opt e1 e2 =
  match e1, e2 with
  | Oconst(Oint(0)), _ -> e2
  | _, Oconst(Oint(0)) -> e1
  | Oconst(Oint(v1)), Oconst(Oint(v2)) -> Oconst(Oint(v1 + v2))
  | _ -> plus e1 e2
let minus_opt e1 e2 =
  match e1, e2 with
  | _, Oconst(Oint(0)) -> e1
  | Oconst(Oint(v1)), Oconst(Oint(v2)) -> Oconst(Oint(v1 - v2))
  | _ -> minus e1 e2
let mult_opt e1 e2 =
  match e1, e2 with
  | Oconst(Oint(1)), _ -> e2
  | _, Oconst(Oint(1)) -> e1
  | Oconst(Oint(v1)), Oconst(Oint(v2)) -> Oconst(Oint(v1 * v2))
  | _ -> mult e1 e2

let local x = Olocal(x)
let global x = Oglobal(x)                      
let var x = Ovar(false, x)
let varmut x = Ovar(true, x)

let ifthenelse c i1 i2 =
  match i1, i2 with
  | Oexp(Oconst(Ovoid)), Oexp(Oconst(Ovoid)) -> Oexp(Oconst(Ovoid))
  | _, Oexp(Oconst(Ovoid)) -> Oif(c, i1, None)
  | _ -> Oif(c, i1, Some(i2))

let sequence i_list =
  let seq i i_list =
    match i, i_list with
    | Oexp(Oconst(Ovoid)), _ -> i_list
    | _, [] -> [i]
    | _ -> i :: i_list in
  let i_list = List.fold_right seq i_list [] in
  match i_list with
  | [] -> Oexp(void)
  | _ -> Osequence i_list
                   
let rec left_state_access lv i_list =
  match i_list with
  | [] -> lv
  | i :: i_list -> left_state_access (Oleft_state_index(lv, local i)) i_list
