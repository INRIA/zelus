(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2018                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* Abstract syntax tree for a Lustre flat kernel *)

open Location
open Ident

type name = string

type op =
  | Lunarypre | Lfby | Lminusgreater | Lifthenelse | Lsharp | Lop of Lident.t

type immediate =
  | Lint of int
  | Lfloat of float
  | Lbool of bool
  | Lchar of char
  | Lstring of string
  | Lvoid

type exp =
  | Llocal of Ident.t
  | Llast of Ident.t
  | Lglobal of Lident.t
  | Lconst of immediate
  | Lconstr0 of Lident.t
  | Lapp of op * exp list
  | Lrecord_access of exp * Lident.t
  | Lrecord of (Lident.t * exp) list
  | Lmerge of exp * (Lident.t * exp) list
  | Lwhen of exp * Lident.t * exp

type clock =
  | Ck_base
  | Ck_on of clock * exp

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
  | Tconstr of Lident.qualident
