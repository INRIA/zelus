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

(* Remove assertions *)

open Zelus

let expression funs acc ({ e_desc } as e) =
  match e_desc with
  | Eassert _ -> { e with e_desc = Econst(Evoid) }, acc
  | _ -> raise Mapfold.Fallback

let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQassert _ -> { eq with eq_desc = EQempty }, acc
  | _ -> raise Mapfold.Fallback
           
let program _ p =
  let funs =
    { Mapfold.defaults with expression; equation } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs () p in
  { p with p_impl_list = p_impl_list }
