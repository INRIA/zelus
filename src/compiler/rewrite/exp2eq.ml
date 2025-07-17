(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* translate some control expressions into equations *)
(* the constructs that are concerned are:
 *- [match e with P1 -> e1 | ... | Pn -> en] =>
    [let match e with P1 -> r = e1 | ... | Pn -> r = en in r]
*- [reset e every c] => let reset r = e every c in r]
*)

open Misc
open Location
open Ident
open Zelus
open Mapfold

let empty = ()

let fresh () = Ident.fresh "r"
    
let expression funs acc e = 
  let ({ e_desc; e_loc } as e), acc = Mapfold.expression funs acc e in
  match e_desc with
  | Ematch { is_size; is_total; e; handlers } ->
     let result = fresh () in
     let handler { m_pat; m_body; m_env; m_loc; m_reset; m_zero } =
       { m_pat; m_body = Aux.id_eq result m_body; m_env; m_loc;
         m_reset; m_zero } in
     let eq =
       { eq_desc = EQmatch { is_size; is_total; e;
                             handlers = List.map handler handlers };
         eq_write = Defnames.singleton result;
         eq_safe = true; eq_index = -1; eq_loc = e_loc } in
     Aux.e_let (Aux.leq false [eq]) (Aux.var result), acc
  | Ereset(e, e_r) ->
     let result = fresh () in
     let eq =
       { eq_desc = EQreset(Aux.id_eq result e, e_r);
         eq_write = Defnames.singleton result;
         eq_safe = true; eq_index = -1; eq_loc = e_loc } in
     Aux.e_let (Aux.leq false [eq]) (Aux.var result), acc
  | _ -> e, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

