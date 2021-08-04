(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Sequential code *)

open Location
open Misc
open Ident

type name = string

type 'a record = { mutable label: Lident.t; arg: 'a }

type ('pattern, 'body) match_handler =
  { m_pat : 'pattern;
    m_body: 'body;
  }

type immediate =
  | Eint of int
  | Eint32 of int
  | Ebool of bool
  | Efloat of float
  | Echar of char
  | Estring of string
  | Evoid
  | Eany
      
type pattern = 
  | Ewildpat
  | Etuplepat of pattern list
  | Evarpat of Ident.t
  | Econstpat of immediate
  | Ealiaspat of pattern * Ident.t
  | Econstr0pat of Lident.t
  | Econstr1pat of Lident.t * pattern list
  | Eorpat of pattern * pattern
  | Erecordpat of (Lident.t * pattern) list

type exp = 
  | Econst of immediate
  | Econstr0 of Lident.t 
  | Econstr1 of Lident.t * exp list
  | Eglobal of Lident.t
  | Elocal of Ident.t
  | Eleftvalue of leftvalue
  | Etuple of exp list
  | Erecord of exp record list
  | Erecord_access of exp record
  | Erecord_with of exp * exp record list 
  | Eif of exp * exp * exp 
  | Ematch of exp * (pattern, exp) match_handler list
  | Elet of pattern * exp * exp
  | Eletvar of Ident.t * Deftypes.typ * exp * exp
  | Eset of leftvalue * exp (* [x.v <- ...] *)
  | Esequence of exp * exp 
  | Eapp of exp * exp list
  | Emethodcall of methodcall * exp option

and leftvalue =
  | Eleft_name of Ident.t
  | Eleft_access of leftvalue * Ident.t
  | Eleft_record_acess of leftvalue * Lident.t
  | Eleft_state_access of leftvalue * mkind
                        
(* Definition of a sequential machine *)
and machine =
  { n_kind: Deftypes.kind; (* combinatorial, continuous-time or discrete-time *)
    n_memories: mentry list;(* its memories *)
    n_instances: ientry list; (* its node instances *)
    n_methods: method_desc list; (* its methods *) 
  }

and mentry =
  { m_name: Ident.t; (* its name *)
    m_value: exp; (* its initial value *)
    m_typ: Deftypes.typ; (* its type *)
    m_kind: mkind; (* the kind of the memory *)
  }

and ientry =
  { i_name: Ident.t; (* its name *)
    i_machine: exp;  (* the machine it belongs to *)
    i_kind: Deftypes.kind; (* the kind of the machine *)
  }
    
and method_desc =
  { me_name: method_name; (* name of the method *)
    me_arg: pattern option; (* its input *)
    me_return: exp; (* its result *)
  }

and methodcall =
  { met_name: method_name; (* name of the method *)
    met_instance: Ident.t; (* name of the instance *)
    met_arg : exp option; (* argument *)
  }

and method_name = name

(* The different kinds of state variables *)
and mkind =
  | Eder (* x.der <- ... *)
  | Econt (* x.pos <- ... *)
  | Ezout (* x.zout <-... *)
  | Ezin (* ... x.zin ... *)
  | Ediscrete (* x <- *)
        
and implementation_list = implementation list

and implementation = 
  | Eletdef of name * exp
  | Emachine of name * pattern list * machine
  | Efun of name * pattern list * exp
  | Eopen of string
  | Etypedecl of (string * string list * type_decl) list

and info = type_expression

(* type declaration *)
and type_expression = 
  | Etypevar of name
  | Etypefun of type_expression * type_expression
  | Etypetuple of type_expression list
  | Etypeconstr of Lident.t * type_expression list

and type_decl =
  | Eabstract_type
  | Eabbrev of type_expression
  | Evariant_type of constr_decl list
  | Erecord_type of (string * type_expression) list
					       
and constr_decl =
  | Econstr0decl of string
  | Econstr1decl of string * type_expression list
