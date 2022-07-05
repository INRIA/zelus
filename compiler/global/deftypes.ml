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
  | Smem : { m_kind: mkind } -> tsort (* a state variable *)

(* the different kinds of internal state variables *)
and mkind =
  | Discrete (* discrete state variable *)
  | Cont (* continous state variable *)
  | Zero (* zero-crossing *)

(** Names written in a block *)
type defnames = 
  { dv: Ident.S.t;  (* [x = ...] *)
    di : Ident.S.t; (* [init x = ...] *)
    der: Ident.S.t; (* [der x = ...] *)}

(* set of names. *)
let names acc { dv; di; der } =
  Ident.S.union dv (Ident.S.union di (Ident.S.union der acc))
let cur_names acc { dv; di } = Ident.S.union dv (Ident.S.union di acc)

(* empty set of defined names *)
(** Making values *)
let empty = { dv = Ident.S.empty; di = Ident.S.empty; der = Ident.S.empty }
let union { dv = dv1; di = di1; der = der1 }
      { dv = dv2; di = di2; der = der2  } =
  { dv = Ident.S.union dv1 dv2;
    di = Ident.S.union di1 di2;
    der = Ident.S.union der1 der2 }
let diff { dv; di; der } names =
  { dv = Ident.S.diff dv names;
    di = Ident.S.diff di names;
    der = Ident.S.diff der names }
let subst { dv; di; der } h =
  let subst names =
    Ident.S.map (fun n -> try Ident.Env.find n h with | Not_found -> n) names in
  { dv = subst dv;
    di = subst di;
    der = subst der }
  

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

let last t_sort =
  match t_sort with
  | Smem _ -> t_sort
  | Sval | Svar | Sstatic -> Smem { m_kind = Discrete }
let init t_sort =
  match t_sort with
  | Smem _ -> t_sort
  | Sval | Svar | Sstatic -> Smem { m_kind = Discrete }
let cont t_sort =
  match t_sort with
  | Smem _ | Sval | Svar | Sstatic -> Smem { m_kind = Cont }
                                  
let desc ty = ty.t_desc
let index ty = ty.t_index

