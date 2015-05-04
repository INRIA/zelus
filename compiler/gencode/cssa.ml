(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* clocked ssa language. Cf. minils in LCTES'08 but where *)
(* only equations are annotated with a clock *)

open Sol
      
type immediate =
  | Cint of int
  | Cint32 of int
  | Cbool of bool
  | Cfloat of float
  | Cchar of char
  | Cstring of string
  | Cvoid

type pattern =
  | Cwildpat
  | Ctuplepat of pattern list
  | Cvarpat of Ident.t
  | Cconstpat of immediate
  | Caliaspat of pattern * Ident.t
  | Cconstr0pat of Lident.t
  | Corpat of pattern * pattern
  | Ctypeconstraintpat of pattern * type_expression
  | Crecordpat of (Lident.t * pattern) list
  
type exp =
  | Cconst of immediate (* immediate constant *)
  | Cconstr0 of Lident.t
  | Cglobal of Lident.t (* global variable *)
  | Clocal of Ident.t
  | Cstate of state (* read of a state variable *)
  | Cindex of exp * exp (* access in an array *)
  | Ctuple of exp list (* tuples *)
  | Capp of Lident.t * exp list (* function application *)
  | Cmethod of method_call * exp list (* call a method Omethod(m, e_list) *)
  | Crecord of (Lident.t * exp) list (* record *)
  | Crecord_access of exp * Lident.t (* access to a record field *)
  | Cifthenelse of exp * exp * exp (* lazy conditional *)
  | Cmatch of exp * (pattern * exp) list (* math/with *)

 and method_call =
   { c_machine: Lident.t; (* the class of the method *)
     c_method_name: method_name; (* the name of the method *)
     c_instance: Ident.t option; (* either a call to self (None) *)
                                 (* or to some instance *)
  }

 and eq =
   { eq_lhs: left;
     eq_rhs: exp;
     eq_clk: clock;
     eq_res: reset }

 and clock =
   | Cbase
   | Con of clock * exp * pattern 

 and reset =
   | Cnever
   | Celse of reset * exp

 and left =
   | Cpat of pattern
   | Cset of state
   
