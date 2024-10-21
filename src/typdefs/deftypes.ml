(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
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
type 'a node =
  { mutable t_desc: 'a;   (* descriptor *)
    mutable t_index: int; (* a number for debugging purpose *)
    mutable t_level: int; (* level for generalisation *)
  }

type typ = typ_desc node

and typ_desc =
  | Tvar
  | Tproduct of typ list
  | Tconstr of Lident.qualident * typ list * abbrev ref
  | Tvec of typ * size
  | Tarrow of { ty_kind: kind; ty_name_opt: Ident.t option;
                ty_arg: typ; ty_res: typ } 
  | Tlink of typ

and is_singleton = bool

and size = 
  | Sint of int
  | Svar of Ident.t
  | Sfrac of { num: size; denom: int }
  | Sop of op * size * size

and op = Splus | Sminus | Smult

and abbrev =
  | Tnil
  | Tcons of typ list * typ

(* type scheme *)
and typ_scheme =
    { typ_vars: typ list;
      mutable typ_body: typ }
	
and typ_instance = { typ_instance : typ list }

and kind =
  | Tfun : vkind -> kind (* combinatorial expression *)
  | Tnode : tkind -> kind (* stateful expression *)

and vkind =
  | Tconst (* value known at compile time *)
  | Tstatic (* value known at instantiation time *)
  | Tany (* dynamically know value *)

and tkind =
  | Tdiscrete (* contains discrete-time state variables *)
  | Tcont (* contains continuous-time state variables *)

(* entry in the typing environment *)
type typentry = 
  { t_path : path; (* [(k1 on ...) on kn x : t] *)
    mutable t_sort: tsort; (* sort *)
    t_tys: typ_scheme (* its type *)
  }

and path = Pkind of kind | Pon of path * kind

and tsort =
  | Sort_val (* a let variable *)
  | Sort_var (* a shared variable *)
  | Sort_mem of mem (* a state variable *)

and mem =
  { m_mkind: mkind option; (* None means discrete-time *)
    m_last: bool; (* [last x] is used *)
    m_init: init; (* is-it initialized? *)
    m_default: init; (* default value *)
  }

and init =
  | No (* no initialisation given *)
  | Eq (* the initial value is given in the body of equations *)
  | Decl of constant option
    (* it is declared with the variable [e.g., ... init e] *)
    (* it is either kept abstract (None) or explicit in the environment *)

and constant = Zelus.immediate

(* the different kinds of internal state variables *)
and mkind =
  | Cont (* continous state variable; position + derivative *)
  | Zero (* zero-crossing *)
  | Horizon (* an event defined as an horizon *)
  | Period (* an event defined as a period *)
  | Encore (* a cascade event *)
  | Major (* true in discrete mode; could we use Encore instead? *)

(* making types *)
let make ty =
  { t_desc = ty; t_level = generic; t_index = Genames.symbol#name }

let no_typ = make (Tproduct [])
let rec is_no_typ { t_desc = desc } =
  match desc with
  | Tproduct [] -> true | Tlink(link) -> is_no_typ link | _ -> false
let no_typ_scheme = { typ_vars = []; typ_body = no_typ }
let no_typ_instance = { typ_instance = [] }
let scheme ty = { typ_vars = []; typ_body = ty }
let no_abbrev () = ref Tnil

(* basic entries for variables *)
let empty_mem = { m_mkind = None; m_last = false; m_init = No; m_default = No }
let initialized mem = { mem with m_init = Eq }
let previous mem = { mem with m_last = true }
let zero mem = Sort_mem { mem with m_mkind = Some Zero }
let horizon mem = Sort_mem { mem with m_mkind = Some Horizon }
let major () = Sort_mem { empty_mem with m_mkind = Some Major }
let imem = initialized empty_mem
let mem = previous imem
let memory = Sort_mem mem
let imemory = Sort_mem imem
		   
let entry k sort t_tys = { t_path = Pkind(k); t_sort = sort; t_tys }

let last t_sort =
  match t_sort with
  | Sort_mem m -> Sort_mem { m with m_last = true }
  | Sort_val | Sort_var -> Sort_mem mem

let init t_sort =
  match t_sort with
  | Sort_mem m -> Sort_mem { m with m_init = Eq }
  | Sort_val | Sort_var -> Sort_mem imem

let cont t_sort =
  match t_sort with
  | Sort_mem m -> Sort_mem { m with m_mkind = Some(Cont) }
  | Sort_val | Sort_var -> Sort_mem { empty_mem with m_mkind = Some(Cont) }
 

let desc ty = ty.t_desc
let index ty = ty.t_index

