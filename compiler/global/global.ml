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
open Deftypes
open Defcaus
open Definit

    
type 'a info = { qualid : Lident.qualident; info : 'a }

(* values in the symbol table *)
type value_desc =
    { mutable value_typ: typ_scheme; (* its type scheme *)
      mutable value_static: bool; (* is-it a static value? *)
      mutable value_caus: tc_scheme option; (* its causality scheme *)
      mutable value_init: ti_scheme option; (* its init. scheme *)
      mutable value_code: value_code; (* source code *)
    }

(** The type of values *)
and value_exp =
  | Vconst of immediate (* constant *)
  | Vconstr0 of Lident.qualident (* constructor *)
  | Vconstr1 of Lident.qualident * value_code list (* constructor *)
  | Vtuple of value_code list (* tuple *)
  | Vrecord of (Lident.qualident * value_code) list (* record *)
  | Vperiod of value_code period (* period *)
  | Vfun of funexp * value_code Env.t
        (* a closure: the function body; the environment of values *)
  | Vabstract of Lident.qualident (* no implementation is given *)

and value_code =
  { value_exp: value_exp; (* the value descriptor *)
    value_name: Lident.qualident option;
                          (* when the value is defined globally *) }

(* Value constructors *)
type constr_desc = { constr_arg: Deftypes.typ list;
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

let value_code value_exp = { value_exp = value_exp; value_name = None }
let value_name n ({ value_exp = value_exp; value_name = opt_name } as v) =
  match opt_name with
  | None -> { v with value_name = Some(n) }
  | Some _ -> v
let value_desc is_static typs qualident = 
  { value_typ = typs; value_static = is_static; value_caus = None; 
    value_init = None; value_code = value_code (Vabstract(qualident)) }
let set_type { info = ({ value_typ = _ } as v) } tys = 
  v.value_typ <- tys
let set_causality { info = ({ value_caus = _ } as v) } tys = 
  v.value_caus <- Some(tys)
let set_init { info = ({ value_init = _ } as v) } tys = 
  v.value_init <- Some(tys)
let set_value_code { info = ({ value_code = _ } as v)} value_code = 
  v.value_code <- value_code

