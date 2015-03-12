(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
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
open Zelus
open Deftypes
open Defcaus

type 'a info = { qualid : Lident.qualident; info : 'a }

(* values in the symbol table *)
type value_desc =
    { value_typ: Deftypes.typ_scheme; (* its type scheme *)
      value_atomic: bool; (* is-it an atomic value? *)
      mutable value_caus: Defcaus.typ_scheme option; (* its causality scheme *)
      mutable value_code: funexp option; (* source code for possible inlining *)
    }

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

let value_desc is_atomic typs = 
  { value_typ = typs; value_atomic = is_atomic; value_caus = None; 
    value_code = None }
let set_causality { info = ({ value_caus = _ } as v) } typs = 
  v.value_caus <- Some(typs)
let set_code { info = ({ value_code = _ } as v)} code = 
  v.value_code <- Some(code)
