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

(* Specialization of recursive size functions *)

(* declarations [let rec f1<<n1,...>> = ... and fk<<<n1,...>> = ...] *)
(* are removed. Fresh functions are introduced for all specialized applications *)
(* that is, f<<s1,...>> where [s1,...] is a list of constant values *)

open Misc
open Location
open Ident
open Zelus

let empty = ()

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with
      global_funs; set_index; get_index; } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list }
