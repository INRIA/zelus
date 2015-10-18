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
type 'a entry = 
    { mutable t_sort: 'a tsort; (* its sort *)
      mutable t_typ: typ (* its type *)
    }

(* variables are defined by local x [[default e | init e ] with op] in ... *)
and 'a tsort =
  | Sval (* a let value *)
  | Svar of 'a var (* a shared variable *)
  | Smem of 'a mem (* a state variable *)

and 'a var =
  { v_combine: 'a option; (* combination function *)
    v_default: 'a option; (* default value *)
  }

and 'a mem =
  { m_kind: mkind option;
    m_next: bool option; (* is-it set with [x = ...] or [next x = ...]? *)
    m_previous: bool; (* [last x] or [x] is used *)
    m_init: 'a option option; (* is-it initialized? *)
    m_combine: 'a option; (* combination function *)
  }

and mkind = Cont | Zero | Horizon | Period | Encore
			    
and constant =
  | Cimmediate of immediate
  | Cglobal of Lident.t

and tentry = constant entry

(** Names written in a block *)
type defnames = 
    { dv: Ident.S.t; (* [x = ...] or [next x = ...] *)
      di: Ident.S.t; (* [init x = ...],[x = ... init ...], *)
                     (* [x = present ... init ...]*)
      der: Ident.S.t; (* [der x = ...] *)
    }

(* set of names. *)
let names acc { dv = dv; di = di; der = der } =
  Ident.S.union acc (Ident.S.union dv (Ident.S.union di der))

let dv acc { dv = dv } = Ident.S.union acc dv
				       
(* empty set of defined names *)
(** Making values *)
let empty = { dv = Ident.S.empty; di = Ident.S.empty; der = Ident.S.empty }

(* introduced names in the [initialization] phase are fully generalized *)
let make desc =
  { t_desc = desc; t_index = - 1; t_level = generic }
let make_realtime desc =
  { t_desc = desc; t_index = - 1; t_level = generic }
let no_typ = make (Tproduct [])
let no_typ_instance = { typ_instance = [] }
let no_abbrev () = ref Tnil

(* basic entries for variables *)
let value = Sval
let variable = Svar { v_combine = None; v_default = None }
let empty_mem = { m_kind = None; m_next = None; m_previous = false;
		  m_init = None; m_combine = None }
let initialized mem = { mem with m_init = Some(None) }
let previous mem = { mem with m_next = Some(false); m_previous = true }
let next mem = { mem with m_next = Some(true); m_previous = false }
let zero mem = Smem { mem with m_kind = Some Zero }
let horizon mem = Smem (previous { mem with m_kind = Some Horizon })
let imem = initialized empty_mem
let mem = previous imem
let memory = Smem mem
let imemory = Smem imem
		   
let entry sort ty = { t_sort = sort; t_typ = ty }

let desc ty = ty.t_desc
let index ty = ty.t_index

