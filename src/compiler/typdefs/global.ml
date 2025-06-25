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

(* global data in the symbol tables *)
open Misc
open Ident
open Zelus

type 'a info = { qualid : Lident.qualident; info : 'a }

type no_info = unit
  
(* values in the symbol table *)
type value_desc =
    { mutable value_typ: Deftypes.typ_scheme; (* its type scheme *)
      mutable value_const: is_const;
      (* is-it a value available at compile time? *)
      mutable value_caus: Defcaus.tc_scheme option; (* its causality scheme *)
      mutable value_init: Definit.ti_scheme option; (* its init. scheme *)
      mutable value_code: value option;
    (* the value is either opaque (None) or transparent (Some(v) *)
}

and is_const = bool

and value =
  | Vconst of immediate (* constant *)
  | Vconstr0 of Lident.qualident (* constructor *)
  | Vconstr1 of Lident.qualident * value list (* constructor *)
  | Vtuple of value list (* tuple *)
  | Vrecord of (Lident.qualident * value) list (* record *)
  | Vclosure of (no_info, no_info) funexp * value Env.t
  (* a closure: the function body; the environment of values *)
  | Vabstract of Lident.qualident (* no implementation is given *)

(* Value constructors *)
type constr_desc =
  { constr_arg: Deftypes.typ list;
    constr_res: Deftypes.typ;
    constr_arity: int }

and label_desc =
    { label_arg: Deftypes.typ; (* if x:arg then x.m: res *)
      label_res: Deftypes.typ; }

type type_desc =
  { mutable type_desc: type_components;
    mutable type_parameters: int list;
  }

and type_components =
    | Abstract_type
    | Variant_type of constr_desc info list
    | Record_type of label_desc info list
    | Abbrev of Deftypes.typ list * Deftypes.typ 
        (* type ('a1,...,'an) t = ty *)

let value_desc is_const typs qualident = 
  { value_typ = typs; value_const = is_const; value_caus = None; 
    value_init = None; value_code = None }
let set_type { info = ({ value_typ } as v) } tys = 
  v.value_typ <- tys
let set_causality { info = ({ value_caus } as v) } tys = 
  v.value_caus <- Some(tys)
let set_init { info = ({ value_init } as v) } tys = 
  v.value_init <- Some(tys)
let set_value_code { info =({ value_code } as v) } value_code =
  v.value_code <- value_code
