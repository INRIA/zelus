(**************************************************************************)
(*                                                                        *)
(*                                Zelus                                   *)
(*               A synchronous language for hybrid systems                *)
(*                       http://zelus.di.ens.fr                           *)
(*                                                                        *)
(*                    Marc Pouzet and Timothy Bourke                      *)
(*                                                                        *)
(*  Copyright 2012 - 2018. All rights reserved.                           *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(*  Zelus is developed in the INRIA PARKAS team.                          *)
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
