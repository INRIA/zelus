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
   | Tvec of typ * size
   | Tfun of kind * Ident.t option * typ * typ 
   | Tlink of typ

and size =
  | Tconst of int
  | Tglobal of Lident.qualident 
  | Tname of Ident.t
  | Top of op * size * size

and op = Tplus | Tminus
		   
and abbrev =
  | Tnil
  | Tcons of typ list * typ

(* type scheme *)
and typ_scheme =
    { typ_vars: typ list;
      mutable typ_body: typ }
	
and typ_instance = { typ_instance : typ list }

and kind =
  | Tstatic of bool (* the argument can be static or not *)
  | Tany | Tcont | Tdiscrete of bool (* statefull or stateless *)
  | Tproba
      
(* entry in the typing environment *)
type tentry = 
    { mutable t_sort: tsort; (* its sort *)
      mutable t_typ: typ (* its type *)
    }

(* variables are defined by local x [[default e | init e ] with op] in ... *)
and tsort =
  | Sstatic (* a static value *)
  | Sval (* a let value *)
  | Svar of var (* a shared variable *)
  | Smem of mem (* a state variable *)

and var =
  { v_combine: Lident.t option; (* combination function *)
    v_default: constant option; (* default value *)
  }

and mem =
  { m_kind: mkind option;
    m_next: bool option; (* None when not set *)
                         (* Some(false) when [... x... = ...] *)
                         (* Some(true) when [next x = ...] *)
    m_previous: bool; (* [last x] or [x] is used *)
    m_init: minit; (* is-it initialized? *)
    m_combine: Lident.t option; (* combination function *)
  }

(* the different kinds of internal state variables *)
and mkind =
  | Cont (* continous state variable; position + derivative *)
  | Zero (* zero-crossing *)
  | Horizon (* an event defined as an horizon *)
  | Period (* an event defined as a period *)
  | Encore (* a cascade event *)
  | Major (* true in discrete mode; could we use Encore instead? *)

and minit =
  | Noinit (* no initialisation given *)
  | InitEq (* the initial value is given in the body of equations *)
  | InitDecl of constant (* it is given at the declaration point *)
      
and constant =
  | Cimmediate of immediate
  | Cglobal of Lident.t

(** Names written in a block *)
type defnames = 
  { dv: Ident.S.t; (* [x = ...] *)
    nv: Ident.S.t; (* [next x = ...] *)
    mv: Ident.S.t; (* [ x += ...] *)
    di: Ident.S.t; (* [init x = ...],[x = ... init ...], *)
                   (* [x = present ... init ...]*)
    der: Ident.S.t; (* [der x = ...] *)
    }

(* set of names. *)
let names acc { dv = dv; di = di; der = der; nv = nv; mv = mv } =
  let acc = Ident.S.union dv acc in
  let acc = Ident.S.union di acc in
  let acc = Ident.S.union der acc in
  let acc = Ident.S.union nv acc in
  Ident.S.union mv acc

let cur_names acc { dv = dv; di = di } =
  Ident.S.union (Ident.S.union acc di) dv


(* empty set of defined names *)
(** Making values *)
let empty =
  { dv = Ident.S.empty; di = Ident.S.empty; der = Ident.S.empty;
    nv = Ident.S.empty; mv = Ident.S.empty }

(* introduced names in the [initialization] phase are fully generalized *)
let make desc =
  { t_desc = desc; t_index = - 1; t_level = generic }
let make_realtime desc =
  { t_desc = desc; t_index = - 1; t_level = generic }
let no_typ = make (Tproduct [])
let rec is_no_typ { t_desc = desc } =
  match desc with
  | Tproduct [] -> true | Tlink(link) -> is_no_typ link | _ -> false
let no_typ_scheme = { typ_vars = []; typ_body = no_typ }
let no_typ_instance = { typ_instance = [] }
let no_abbrev () = ref Tnil

(* basic entries for variables *)
let static = Sstatic
let value = Sval
let variable = Svar { v_combine = None; v_default = None }
let empty_mem = { m_kind = None; m_next = None; m_previous = false;
		  m_init = Noinit; m_combine = None }
let initialized mem = { mem with m_init = InitEq }
let previous mem = { mem with m_next = Some(false); m_previous = true }
let next mem = { mem with m_next = Some(true); m_previous = false }
let zero mem = Smem { mem with m_kind = Some Zero }
let horizon mem = Smem (previous { mem with m_kind = Some Horizon })
let major () = Smem { empty_mem with m_kind = Some Major }
let default v_opt c_opt = Svar { v_combine = c_opt; v_default = v_opt }
let imem = initialized empty_mem
let cmem c_opt mem = { mem with m_combine = c_opt }
let mem = previous imem
let memory = Smem mem
let imemory = Smem imem
		   
let entry sort ty = { t_sort = sort; t_typ = ty }

let desc ty = ty.t_desc
let index ty = ty.t_index

