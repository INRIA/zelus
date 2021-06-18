(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* type definition *)

open Misc
open Lident

type name = string

(* types *)
type 'a loc =
  { mutable t_desc: 'a;   (* descriptor *)
    mutable t_index: int; (* a number for debugging purpose *)
    mutable t_level: int; (* level for generalisation *)
  }

type typ = typ_desc loc

 and typ_desc =
   | Tvar
   | Tproduct of typ list
   | Tconstr of Lident.qualident * typ list * abbrev ref
   | Tarrow of kind * typ * typ 
   | Tlink of typ

		   
and abbrev =
  | Tnil
  | Tcons of typ list * typ

(* type scheme *)
and typ_scheme =
    { typ_vars: typ list;
      mutable typ_body: typ }
	
and typ_instance = { typ_instance : typ list }

and kind =
  | Tfun
  | Tnode
  | Tstatic
      
(* entry in the typing environment *)
type 'a tentry = 
  { mutable t_sort: tsort; (* sort *)
    mutable t_default: 'a option; (* default value *)
    mutable t_init: 'a option; (* init value *)
    mutable t_typ: typ (* its type *)
  }

and tsort =
  | Sstatic (* a static variable *)
  | Sval (* a let variable *)
  | Svar (* a shared variable *)
  | Smem (* a state variable *)

(** Names written in a block *)
type defnames = 
  { dv: Ident.S.t; (* [x = ...] *)
  }

(* set of names. *)
let names acc { dv = dv } = Ident.S.union dv acc
let cur_names acc { dv = dv } = Ident.S.union dv acc

(* empty set of defined names *)
(** Making values *)
let empty = { dv = Ident.S.empty }

(* introduced names in the [initialization] phase are fully generalized *)
let make desc =
  { t_desc = desc; t_index = - 1; t_level = generic }

let no_typ = make (Tproduct [])
let rec is_no_typ { t_desc = desc } =
  match desc with
  | Tproduct [] -> true | Tlink(link) -> is_no_typ link | _ -> false
let no_typ_scheme = { typ_vars = []; typ_body = no_typ }
let no_typ_instance = { typ_instance = [] }
let no_abbrev () = ref Tnil

let desc ty = ty.t_desc
let index ty = ty.t_index

