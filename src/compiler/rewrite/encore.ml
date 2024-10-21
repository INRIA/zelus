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

(* When an event (zero-crossing or time horizon) occurs and changes *)
(* a non local discrete state variable [x] (a variable for which *)
(* [last x] exists), an extra step must be done *)
(* [match e with | P1 -> (* zero *) x = ... | Pn -> ...] *)
(* is rewritten: *)
(* [local horizon h default +infinity do
     match e with | P1 -> do h = 0.0 and x = ... | ... *)

(* not finished; it is better to  *)

open Ident
open Zelus
open Aux
open Defnames
open Mapfold

type acc =
  { last: S.t; (* set of variables [x] for which [last x] is used *)
    horizon: Ident.t option; (* horizon that has been added *)
  }

let empty = { last = S.empty; horizon = None }

let fresh () = Ident.fresh "encore"

(* [local h default infinity do ... done *)
let local_in_eq { horizon } eq =
  match horizon with
  | None -> eq
  | Some(h) ->
     Aux.eq_local
       (Aux.block_make [Aux.vardec h false None (Some(Aux.infinity))]
          [eq])

(* [local h default infinity do m = e in m *)
let local_in_exp { horizon } e =
  match horizon with
  | None -> e
  | Some(h) ->
     let m = fresh () in
     Aux.e_local
       (Aux.block_make [Aux.vardec h false None (Some(Aux.infinity));
                        Aux.vardec m false None None]
       [Aux.id_eq m e])  (Aux.var m)

(* Does a block contains an equation [x = e] on a last variable? *)
let encore { last } { dv } = not (S.is_empty (S.inter last dv))

(* Add an equation [horizon = 0.0] *)
let add_zero ({ horizon } as acc) ({ eq_write } as eq) =
  if encore acc eq_write then
    let h, horizon =
      match horizon with
      | None -> let h = fresh () in h, Some(h) | Some(h) -> h, horizon in
    let eq = Aux.eq_and (id_eq h Aux.zero) eq in
    eq, { acc with horizon }
  else
    eq, acc

let vardec funs acc vdec =
  let ({ var_name; var_is_last } as vdec), ({ last } as acc) =
    Mapfold.vardec funs acc vdec in
  vdec, { acc with last = S.add var_name last }

(* Translation of equations *)
let equation funs acc eq =
  let { eq_desc } as eq, acc = Mapfold.equation funs acc eq in
  match eq_desc with 
  | EQmatch({ handlers } as m) ->
     (* add an equation [h = 0.0] if at least one branch is activated *)
     (* on a zero-crossing and changes a non local state variable [x] *)
     (* where [last x] is also read *)
     let handlers, acc =
       Util.mapfold
	 (fun acc ({ m_zero; m_body } as m_h) ->
	   let m_body, acc =
	     if m_zero then add_zero acc m_body
             else m_body, acc in
           { m_h with m_body }, acc) acc handlers in
     { eq with eq_desc = EQmatch { m with handlers } }, acc
    | _ -> eq, acc

let result funs acc ({ r_desc } as r) =
  (* introduce a fresh horizon when necessary *)
  let r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc_local = Mapfold.expression_it funs empty e in
       Exp(local_in_exp acc_local e), acc
    | Returns(b) ->
       let { b_body } as b, acc_local = Mapfold.block_it funs empty b in
       Returns { b with b_body = local_in_eq acc_local b_body }, acc in
  { r with r_desc }, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = { Mapfold.default_global_funs with build } in
  let funs =
    { Mapfold.defaults with vardec; equation; result; set_index; get_index;
                            global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
