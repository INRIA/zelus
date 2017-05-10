(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* global data in the symbol tables *)
open Misc
open Ident
open Zelus
open Deftypes
open Defcaus

type 'a info = { qualid : Lident.qualident; info : 'a }

(* values in the symbol table *)
type value_desc =
    { mutable value_typ: Deftypes.typ_scheme; (* its type scheme *)
      mutable value_static: bool; (* is-it a static value? *)
      mutable value_caus: Defcaus.tc_scheme option; (* its causality scheme *)
      mutable value_code: value_code; (* source code *)
    }

(** The type of values *)
and value_exp =
  | Vconst of immediate (* constant *)
  | Vconstr0 of Lident.qualident (* constructor *)
  | Vtuple of value_code list (* tuple *)
  | Vrecord of (Lident.qualident * value_code) list (* record *)
  | Vperiod of period (* period *)
  | Vfun of funexp * value_code Env.t (* a closure *)
  | Vabstract of Lident.qualident (* no implementation is given *)

and value_code =
  { value_exp: value_exp; (* the value descriptor *)
    value_name: Lident.qualident option;
                          (* when the value is defined globally *) }

(* Value constructors *)
type constr_desc = { constr_res: Deftypes.typ }

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

let value_code value_exp = { value_exp = value_exp; value_name = None }
let value_name n ({ value_exp = value_exp; value_name = opt_name } as v) =
  match opt_name with
  | None -> { v with value_name = Some(n) }
  | Some _ -> v
let value_desc is_static typs qualident = 
  { value_typ = typs; value_static = is_static; value_caus = None; 
    value_code = value_code (Vabstract(qualident)) }
let set_type { info = ({ value_typ = _ } as v) } typs = 
  v.value_typ <- typs
let set_causality { info = ({ value_caus = _ } as v) } typs = 
  v.value_caus <- Some(typs)
let set_value_code { info = ({ value_code = _ } as v)} value_code = 
  v.value_code <- value_code
