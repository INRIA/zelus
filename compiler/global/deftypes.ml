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

(* type definition *)

open Misc
open Lident

type immediate =
  | Eint of int
  | Efloat of float
  | Ebool of bool
  | Echar of char
  | Estring of string
  | Evoid

type name = string

(* types *)
type typ =
  { mutable t_desc: typ_desc;  (* descriptor *)
    mutable t_index: int;      (* a number for debugging purpose *)
    mutable t_level: int;      (* level for generalisation *)
  }

and typ_desc =
  | Tvar
  | Tproduct of typ list
  | Tconstr of Lident.qualident * typ list * abbrev ref
  | Tlink of typ

and abbrev =
  | Tnil
  | Tcons of typ list * typ

(* type scheme *)
and typ_scheme =
    { typ_vars: typ list;
      mutable typ_body: typ_body }

and typ_body =
    | Tvalue of typ
    | Tsignature of kind * bool * typ list * typ

and instance =
  { typ_instance: typ list }

and kind = Tany | Tcont | Tdiscrete of bool (* statefull or stateless *)

(* entry in the typing environment *)
type tentry = 
    { mutable t_sort: tsort; (* its sort *)
      mutable t_typ: typ (* its type *)
    }

and tsort = 
  | Val (* a value. [last x] is forbidden *)
  | ValDefault of immediate 
        (* a value. [last x] is forbidden. Default value is [false] *)
  | Mem of tmem

(** a memory variable. Either change the current value or the next one *)
(** Invariant: m.t_last_is_used => not(m.t_next_is_set) *)
(**         /\ m.t_is_set => not(m.t_next_is_set)  *)
and tmem =
    { t_last_is_used: bool; (* [last x] appears *)
      t_der_is_defined: bool; (* [der x = ...] appears *)
      t_initialized: bool;  (* [init x = ...] appears *)
      t_is_set: bool; (* [x = ...] appears *)
      t_next_is_set: bool; (* [next x = ...] appears *)
      t_default: default; (* what to do when no equation is given *)
    }

(* treatment to be done when an equation is absent in a branch *)
and default = 
  | Previous (* complement with [x = last x] *)
  | Default (* produce a default value *)
  | Absent (* do nothing. This is the case for signals *)

(** Names written in a block *)
type defnames = 
    { dv: Ident.S.t; (* [x = ...] or [next x = ...] *)
      di: Ident.S.t; (* [init x = ...],[x = ... init ...], *)
                     (* [x = present ... init ...]*)
      dr: Ident.S.t; (* [der x = ...] *)
    }


(* introduced names in the [initialization] phase are fully generalized *)
let make desc =
  { t_desc = desc; t_index = - 1; t_level = generic }
let make_realtime desc =
  { t_desc = desc; t_index = - 1; t_level = generic }
let no_typ = make (Tproduct [])
let no_typ_instance = { typ_instance = [] }
let no_abbrev () = ref Tnil

(* basic values for memories. By default, they are initialized *)
let discrete_memory = { t_initialized = true; t_last_is_used = true;
			t_der_is_defined = false; t_is_set = true;
			t_next_is_set = false; t_default = Previous }
let continuous_memory = { t_initialized = true; t_last_is_used = true;
			t_der_is_defined = true; t_is_set = true;
			t_next_is_set = false; t_default = Default }

let desc ty = ty.t_desc
let index ty = ty.t_index

