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

(* Abstract syntax tree for a basic Lustre used for formal *)
(* verification. No node instance; no constrol structure. *)
(* clocks are kept in case of a translation into Lustre but are *)
(* only necessary for the change of state variables *)

open Location
open Ident

type name = string

type op =
  | Lunarypre (* un-initialized unit delay *)
  | Lfby (* initialized unit delay *)
  | Lminusgreater (* initialization *)
  | Lifthenelse (* strict conditional *)
  | Lsharp (* n-ary, pairwise xor *)
  | Lop of Lident.t (* call of a combinatorial function *)

type immediate =
  | Lint of int
  | Lfloat of float
  | Lbool of bool
  | Lchar of char
  | Lstring of string
  | Lvoid

type constr0pat =
  | Lconstr0pat of Lident.t
  | Lboolpat of bool

type exp =
  | Llocal of Ident.t
  | Llast of Ident.t
  | Lglobal of Lident.t
  | Lconst of immediate
  | Lconstr0 of Lident.t
  | Lapp of op * exp list
  | Lrecord_access of exp * Lident.t
  | Lrecord of (Lident.t * exp) list
  | Ltuple of exp list
  | Lget of exp * int
  | Lmerge of exp * (constr0pat * exp) list
  | Lwhen of exp * constr0pat * exp

type clock =
  | Ck_base (* true *)
  | Ck_on of clock * constr0pat * exp (* ck on C(c) *)

type reset =
  | Res_never
  | Res_else of reset * exp

type eq =
    { eq_kind: kind;
      eq_ident: Ident.t;
      eq_exp: exp;
      eq_clock: clock }

and kind =
  | Def
  | Init of reset
  | Next
    
type funexp =
  { f_inputs: Ident.t list;
    f_output: Ident.t;
    f_env: tentry Env.t;
    f_body: eq list;
    f_assert: exp list; }
  
and tentry =
  { t_typ: typ }
  
and implementation =
  | Lconstdecl of name * exp
  | Lfundecl of name * funexp
  | Ltypedecl of name * type_decl
                 
and type_decl =
  | Labstract_type
  | Lvariant_type of name list
  | Lrecord_type of (name * typ) list

and typ =
  | Tint | Tbool | Tfloat | Tchar | Tstring | Tunit
  | Tconstr of Lident.qualident | Tproduct of typ list
