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

(* complete branches with a default value [der x = 0.0] for state variables *)
(* This step is applied to normalised equations. *)
(* read/write information must be correct *)

open Zelus
open Ident
open Defnames
open Aux
open Mapfold

let der_eq_zero x = Aux.eq_der x zero

(* complete a set of equations with default equations for every *)
(* variable from [der] which is not defined in [w] *)
(* [match e with ...| Pi -> eqi | ...] writes der =>
    match e with ...| Pi -> der x = 0.0 and ... eqi | ...] if x in der\der(eqi) *)
let complete { der = der_global} ({ eq_desc; eq_write } as eq) =
  let l = S.diff der_global eq_write.der in
  let eq_list = S.fold (fun x acc -> (der_eq_zero x) :: acc) l [eq] in
  Aux.par eq_list

let equation funs acc eq =
  let { eq_desc; eq_write } as eq, acc = Mapfold.equation funs acc eq in
  match eq_desc with
  | EQif { e; eq_true; eq_false } ->
     let eq_true = complete eq_write eq_true in
     let eq_false = complete eq_write eq_false in
     { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
  | EQmatch({ e; handlers } as m) ->
     let handler ({ m_body } as m_h) =
       let m_body = complete eq_write m_body in
       { m_h with m_body } in
     let e, acc = funs.expression funs acc e in
     let handlers = List.map handler handlers in
     { eq with eq_desc = EQmatch { m with e; handlers } }, acc
  | _ -> eq, acc

let program genv0 p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; global_funs } in
  let p, _ = Mapfold.program_it funs genv0 p in
  p
