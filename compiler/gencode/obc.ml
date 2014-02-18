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
(* abstract syntax tree of the object code *)

open Location
open Misc
open Ident

type name = string

type sort = Val | Var | Mem

type 'a localized =
    { desc: 'a;
      loc: location }

type exp = edesc localized

and edesc =
  | Oconst of immediate
  | Oconstr0 of Lident.t
  | Oconstr1 of Lident.t * exp list
  | Oglobal of Lident.t
  | Olocal of Ident.t * sort
  | Oarray_element of Ident.t * exp
  | Otuple of exp list
  | Oapp of Lident.t * exp list
  | Ostep of Lident.t * Ident.t * exp list
  | Oreset of Lident.t * Ident.t
  | Orecord of (Lident.t * exp) list
  | Orecord_access of exp * Lident.t
  | Otypeconstraint of exp * type_expression
  | Olet of (pattern * exp) list * exp
  | Oletvar of Ident.t * Deftypes.typ * exp option * exp
  | Oifthenelse of exp * exp * exp
  | Ofor of bool * Ident.t * exp * exp * exp
  | Omatch of exp * match_handler list
  | Oassign of left_value * sort * exp
  | Oarray_assign of Ident.t * exp * exp
  | Osequence of exp * exp
      
and left_value = Ident.t
    
and immediate =
  | Oint of int
  | Oint32 of int
  | Obool of bool
  | Ofloat of float
  | Ochar of char
  | Ostring of string
  | Ovoid

and pattern = pdesc localized

and pdesc =
  | Owildpat
  | Otuplepat of pattern list
  | Ovarpat of Ident.t
  | Oconstpat of immediate
  | Oaliaspat of pattern * Ident.t
  | Oconstr0pat of Lident.t
  | Oconstr1pat of Lident.t * pattern list
  | Oorpat of pattern * pattern
  | Otypeconstraintpat of pattern * type_expression
  | Orecordpat of (Lident.t * pattern) list
      
and match_handler =
    { w_pat  : pattern;
      w_body : exp; }
      
and machine = 
    { m_memories: (Ident.t * (Deftypes.typ * exp option)) list; (* memories *)
      m_instances: (Ident.t * Lident.t) list; (* instances *)
      m_step: pattern list * exp; (* method step for computing one reaction *)
      m_reset: exp; (* method to reset the internal state *)
    }

and implementation_list = implementation list

and implementation = implementation_desc localized

and implementation_desc =
    | Oletvalue of name * exp
    | Oletfun of name * pattern list * exp
    | Oletmachine of name * machine
    | Oopen of string
    | Otypedecl of (string * string list * type_decl) list

(* type declaration *)
and type_expression = type_expression_desc localized

and type_expression_desc =
    | Otypevar of string
    | Otypearrow of type_expression * type_expression
    | Otypetuple of type_expression list
    | Otypeconstr of Lident.t * type_expression list
    | Otypeobject of (name * type_expression) list

and type_decl =
    | Oabstract_type
    | Oabbrev of type_expression
    | Ovariant_type of constr_decl list
    | Orecord_type of (string * type_expression) list

and constr_decl =
    | Oconstr0decl of string
    | Oconstr1decl of string * type_expression list

let make desc = { desc = desc; loc = no_location }
