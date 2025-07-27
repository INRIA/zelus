(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
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

(* memoization table; mapping [id -> (s1,...,sn) -> id_j] *)
(* where [s1,...,sn] are integer values *)
module Memo = 
  Map.Make (struct type t = int list let compare = Stdlib.compare end)

type 'a info = { qualid : Lident.qualident; info : 'a }

type no_info = unit
  
(* values in the symbol table *)
type value_desc =
    { mutable value_typ: Deftypes.typ_scheme; (* its type scheme *)
      mutable value_const: is_const;
      (* is-it a value available at compile time? *)
      mutable value_caus: Defcaus.tc_scheme option; (* its causality scheme *)
      mutable value_init: Definit.ti_scheme option; (* its init. scheme *)
      mutable value_exp: vexp option;
    (* the value is either opaque (None) or transparent (Some(v) *)
}

and is_const = bool

and vexp =
  | Vfun of funexp
  | Vsizefun of sizefun

and funexp =
  { f_inline: bool; (* the function call must be inlined *)
    f_args: Typinfo.arg list; (* list of arguments *)
    f_kind: Zelus.kind; (* kind of the function *)
    f_body: Typinfo.result; (* the body of the function *)
    f_env: Typinfo.ienv Env.t; (* the environment for parameters *)
 }

and sizefun =
{ (* size function: [sf_id <<n1,...>> = e] *)
    sizefun: Typinfo.sizefun;
    (* the list of specialized functions *)
    mutable sizefun_specialized: (Ident.t * Typinfo.exp) list;
    (* the memoization table which associate a fresh name [id] to (s1,...,sn) *)
    sizefun_memo_table: Ident.t Memo.t;
    (* [sf_id] used or not in the code *)
    mutable sizefun_used: bool;
  }

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
    value_init = None; value_exp = None }
let set_type { info = ({ value_typ } as v) } tys = 
  v.value_typ <- tys
let set_causality { info = ({ value_caus } as v) } tys = 
  v.value_caus <- Some(tys)
let set_init { info = ({ value_init } as v) } tys = 
  v.value_init <- Some(tys)
let set_value_exp { info = ({ value_exp } as v) } value_exp' =
  v.value_exp <- Some(value_exp')
