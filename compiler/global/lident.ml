(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
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
