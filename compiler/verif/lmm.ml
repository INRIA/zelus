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

 and p_kind = Estatic | Evar | Einit of expression

 and implementation =
   { impl_desc: impl_desc;
     impl_loc: location }

 and impl_desc =
   | Econstdecl of name * exp
   | Efundecl of name * funexp
			  
