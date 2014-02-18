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
      mutable value_cont: cont_desc; (* size of the continuous state *)
      mutable value_code: funexp option; (* source code for possible inlining *)
    }

(* the internal representation of the continuous state *)
(* passed to a function *)
and cont_desc =
    { c_period: discrete option; (* how internal periods have been compiled *)
      c_state: state_repr option; (* the internal representation of cont. states *)
    }

and discrete = bool

and state_repr =
  | Ctuple of Deftypes.typ * Deftypes.typ (* continous state and zero-crossing *)
  | Cflat of int * int (* the size of the continuous state vector and zero-crossing *)

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

exception Period_desc_not_set
exception Cont_desc_not_set

let value_desc is_atomic typs = 
  { value_typ = typs; value_atomic = is_atomic; value_caus = None;
    value_cont = { c_period = None; c_state = None }; value_code = None }
let set_causality { info = ({ value_caus = _ } as v) } typs = 
  v.value_caus <- Some(typs)
let set_code { info = ({ value_code = _ } as v)} code = 
  v.value_code <- Some(code)
let set_period_desc { info = ({ value_cont } as v)} p =
  v.value_cont <- { value_cont with c_period = p }
let set_cont_desc { info = ({ value_cont } as v)} c =
  v.value_cont <- { value_cont with c_state = c }

(* added by cyprien *)
let set_discrete { info = ({ value_typ = { typ_body = typ_body } } as v) } =
  match typ_body with 
    | Tvalue(typ) -> failwith("tvalue. expected signature")
    | Tsignature(k,b,l,t2) -> 
        v.value_typ.typ_body <-  Tsignature(Tdiscrete(true),b,l,t2)


let period_desc { info = { value_cont = { c_period } } } =
  match c_period with
  | None -> raise Period_desc_not_set
  | Some p -> p

let cont_desc { info = { value_cont = { c_state } } } =
  match c_state with
  | None -> raise Cont_desc_not_set
  | Some cs -> cs

