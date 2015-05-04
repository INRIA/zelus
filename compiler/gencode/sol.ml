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

(* abstract syntax tree of the generic object code *)

type sort = 
  | Oval (* local variable with a single write *)
  | Ovar (* shared variable with possibly several writes *)
  | Omem of mem (* state variable *)

and mem =
  | Odiscrete (* discrete state variable *)
  | Ozero (* zero-crossing variable with its size *)
  | Ocont (* continuous-state variable with its size *)
	
(* a continuous state variable [x] is pair of arrays *)
(* with two fields: [x.der] for its derivative. [x.pos] for its current value. *)
(* a zero-crossing variable [x] has two field: [x.zin] is true when *)
(* the solver has detected a zero-crossing. [x.zout] is the value *)
(* to be observed for a zero-crossing *)

and state =
  | Oself
  | Oname of Ident.t
  | Oinstance of Ident.t
  | Oprimitive of state * primitive
  
(* a machine provides certain fields for reading/writting special values *)
and primitive =
  | Oder (* x.der.(i) <- ... *)
  | Opos (* x.pos.(i) <- ... *)
  | Ozout (* x.zout.(i) <-... *)
  | Ozin (* ... x.zin.(i) ... *)

and immediate =
  | Oint of int
  | Oint32 of int
  | Obool of bool
  | Ofloat of float
  | Ochar of char
  | Ostring of string
  | Ovoid

(* implementation of a generic machine. The body of method is generic *)
type ('exp, 'eq) machine =
    { m_kind: Deftypes.kind;
      m_memories:
	(Ident.t * (mem * Deftypes.typ * 'exp option)) list; (* memories *)
      m_instances: (Ident.t * Lident.t * Deftypes.kind) list; (* instances *)
      m_methods: 'eq method_desc list; (* the list of methods *) 
    }

and 'eq method_desc =
   { m_name: method_name;
     m_param: Ident.t list;
     m_body: 'eq } 

and method_name = 
  | Ostep (* computes values and possible changes of states *)
  | Oreset (* resets the discrete state *)
  | Oderivatives (* computes the values of derivatives *)
  | Ocrossings (* computes the zero-crossing functions *)
  | Omaxsize (* returns the size of the cvector and zvector *)
  | Oreinit (* should we re-init the solver? *)
  | Ocin | Ocout (* copies the continuous state vector *)
  | Odout | Oczin | Oclear_zin | Oczout(* copies derivatives and zero crossings *)
  | Ocsize | Ozsize (* current size for cont. states and zero crossings *)

and ('exp, 'eq) implementation =
    | Oletvalue of string * 'exp
    | Oletfun of string * Ident.t list * 'exp
    | Oletmachine of string * ('exp, 'eq) machine
    | Oopen of string
    | Otypedecl of (string * string list * type_decl) list

(* type declaration *)
and type_expression =
    | Otypevar of string
    | Otypearrow of type_expression * type_expression
    | Otypetuple of type_expression list
    | Otypeconstr of Lident.t * type_expression list
    | Otypeobject of (string * type_expression) list

and type_decl =
    | Oabstract_type
    | Oabbrev of type_expression
    | Ovariant_type of constr_decl list
    | Orecord_type of (string * type_expression) list

and constr_decl =
    | Oconstr0decl of string
    | Oconstr1decl of string * type_expression list
