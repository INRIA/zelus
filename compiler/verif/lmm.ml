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
(* Abstract syntax tree for a Lustre flat kernel *)

open Location
open Ident
open Deftypes

type 'a localized = { desc: 'a; loc: Location.location }

type kind = A | D

type expression =
    { e_desc: desc;
      e_loc: location;
      e_typ: Deftypes.typ
    }
      
 and desc =
   | Elocal of Ident.t
   | Eglobal of Lident.t
   | Econst of immediate
   | Econtr0 of Lident.t
   | Eapp of op * exp list
   | Erecord_access of exp * Lident.t
   | Erecord of (Lident.t * exp) list
				 
 and op =
   | Eunarypre | Eminusgreater | Eifthenelse | Eop of Lident.t
							
 and immediate = Deftypes.immediate
		   
 and pattern =
   | Etuplepat of pat list
   | Evarpat of Ident.t
		  
 and eq =
   { eq_lhs: pat;
     eq_rhs: expression;
     eq_loc: location }
     
 and funexp =
   { f_kind: kind;
     f_inputs: param list;
     f_outputs: param list;
     f_local: param list;
     f_body: eq list }

 and param =
   { p_kind: pkind;
     p_name: Ident.t;
     p_loc: location }

 and pkind =
   | Estatic | Evar | Einit of expression

 and implementation = implementation_desc localized

 and implementation_desc =
   | Econstdecl of name * exp
   | Efundecl of name * funexp
   | Etypedecl of name * type_decl

 and type_decl =
   | Eabstract_type
   | Eabbrev of type_expression
   | Evariant_type of name list
   | Erecord_type of (name * type_expression) list

 and type_expression = type_expression_desc localized

 and type_expression_desc =
   | Etypevar of string
			  
