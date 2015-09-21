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
(* abstract syntax tree of the object code *)

open Location
open Misc
open Ident

type name = string

type sort = 
  | Val (* local variable with a single write *)
  | Var (* shared variable with possibly several writes *)
  | Mem of mem (* state variable *)

and mem =
  | Discrete (* discrete state variable *)
  | Zero (* zero-crossing variable with its size *)
  | Cont (* continuous-state variable with its size *)
  | Horizon (* horizon *)
  | Encore (* should we do an extra step *)
  | Period (* period *)
      
(* a continuous state variable [x] is pair of arrays *)
(* with two fields: [x.der] for its derivative. [x.pos] for its current value. *)
(* a zero-crossing variable [x] has two field: [x.zin] is true when *)
(* the solver has detected a zero-crossing. [x.zout] is the value *)
(* to be observed for a zero-crossing *)

type 'a localized =
    { desc: 'a;
      loc: location }

type exp = edesc localized

and edesc =
  | Oconst of immediate (* immediate constant *)
  | Oconstr0 of Lident.t (* 0-ary and 1-ary constructor *)
  | Oconstr1 of Lident.t * exp list
  | Oglobal of Lident.t (* global variable *)
  | Olocal of Ident.t * is_shared (* read of local variable *)
  | Ostate of left_state_value (* read of a state variable *)
  | Oindex of exp * exp (* access in an array *)
  | Otuple of exp list (* tuples *)
  | Oapp of Lident.t * exp list (* function applicatin *)
  | Omethod of method_call * exp list
           (* call a method Omethod(m, e_list) *)
  | Orecord of (Lident.t * exp) list (* record *)
  | Orecord_access of exp * Lident.t (* access to a record field *)
  | Otypeconstraint of exp * type_expression (* type constraint *)
  | Olet of (pattern * exp) list * exp (* local definition of values *)
  | Oletvar of Ident.t * Deftypes.typ * exp option * exp (* local variables *)
  | Oifthenelse of exp * exp * exp (* lazy conditional *)
  | Ofor of bool * Ident.t * exp * exp * exp (* for loop *)
  | Owhile of exp * exp (* while loop *)
  | Omatch of exp * exp match_handler list (* math/with *)
  | Oassign of left_value * exp (* assignment to a local variable *)
  | Oassign_state of left_state_value * exp (* assignment to a state variable *)
  | Osequence of exp * exp (* sequence *)

and method_call =
  { c_machine: Lident.t; (* the class of the method *)
    c_method_name: method_name; (* the name of the method *)
    c_instance: Ident.t option; (* either a call to self (None) *)
                                (* or to some instance *)
  }

and is_shared = bool

and left_value = 
  | Oleft_name of Ident.t
  | Oleft_record_access of left_value * Lident.t
  | Oleft_index of left_value * exp
  
and left_state_value =
  | Oself
  | Oleft_state_global of Lident.t 
  | Oleft_instance_name of Ident.t
  | Oleft_state_name of Ident.t
  | Oleft_state_record_access of left_state_value * Lident.t
  | Oleft_state_index of left_state_value * exp
  | Oleft_state_primitive_access of left_state_value * primitive_access

(* a machine provides certain fields for reading/writting special values *)
and primitive_access =
  | Oder (* x.der.(i) <- ... *)
  | Ocont (* x.pos.(i) <- ... *)
  | Ozero_out (* x.zero_out.(i) <-... *)
  | Ozero_in (* ... x.zero_in.(i) ... *)

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
      
and 'a match_handler =
    { w_pat  : pattern;
      w_body : 'a; }
      
(* implementation of a machine *)
and machine =
    { m_kind: Deftypes.kind;
      m_memories:
	(Ident.t * (mem * Deftypes.typ * exp option)) list; (* memories *)
      m_instances: (Ident.t * Lident.t * Deftypes.kind) list; (* instances *)
      m_methods: method_desc list; (* the list of methods *) 
    }

and method_desc =
   { m_name: method_name;
     m_param: pattern list;
     m_body: exp } 

and method_name = 
  | Ostep (* computes values and possible changes of states *)
  | Oreset (* resets the discrete state *)
  | Oderivatives (* computes the values of derivatives *)
  | Ocrossings (* computes the zero-crossing functions *)
  | Omaxsize (* returns the size of the cvector and zvector *)
  | Oreinit (* should we re-init the solver? *)
  | Ocin | Ocout (* copies the continuous state vector *)
  | Odout | Ozin | Oclear_zin | Ozout (* copies derivatives and zero crossings *)
  | Odzero (* resets the internal derivatives *)
  | Ocsize | Ozsize (* current size for cont. states and zero crossings *)
  | Ohorizon (* next horizon *)
      
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
