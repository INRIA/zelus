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

(* long identifiers *)
type t =
    | Name of string
    | Modname of qualident

and qualident = { qual: string; id: string }

let qualidname { qual = m; id = id } = m ^ "." ^ id

let modname = function
  | Name(n) -> n
  | Modname(qualid) -> qualidname qualid

let source = function
  | Name(n) -> n
  | Modname(qualid) -> qualid.id

let fprint_t ff id = Format.fprintf ff "%s" (modname id)

let compare = compare
