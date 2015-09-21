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

(* abstract syntax tree of the dataflow code with modes *)

type mem =
  | Odiscrete (* discrete state variable *)
  | Ozero (* zero-crossing variable with its size *)
  | Ocont (* continuous-state variable with its size *)
  | Operiod (* period *)
      
(* a continuous state variable [x] is pair of arrays *)
(* with two fields: [x.der] for its derivative. [x.pos] for its current value. *)
(* a zero-crossing variable [x] has two field: [x.zin] is true when *)
(* the solver has detected a zero-crossing. [x.zout] is the value *)
(* to be observed for a zero-crossing *)

and state =
  | Oself
  | Oname of is_last * Ident.t
  | Oinstance of Ident.t
  | Oprimitive of state * primitive

and is_last = bool
		
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
  
and exp =
  | Cconst of immediate (* immediate constant *)
  | Cconstr0 of Lident.t
  | Cglobal of Lident.t (* global variable *)
  | Clocal of Ident.t (* local variable *)
  | Cindex of exp * exp (* access in an array *)
  | Ctuple of exp list (* tuples *)
  | Capp of op * exp list (* function application *)
  | Crecord of (Lident.t * exp) list (* record *)
  | Crecord_access of exp * Lident.t (* access to a record field *)
  | Cifthenelse of exp * exp * exp (* lazy conditional *)
  | Cmatch of exp * (pattern * exp) list (* math/with *)

and op =
  | Cop of Lident.t
  | Cmethod of Lident.t * method_name * Ident.t option
	     (* the class of the method, the method and the instance *)


(* implementation of a generic machine. The body of method is generic *)
and 'eq machine =
    { m_kind: Deftypes.kind;
      m_memories: mentry Ident.Env.t; (* memories *)
      m_instances: ientry Ident.Env.t; (* instances *)
      m_methods: 'eq method_desc list; (* the list of methods *) 
    }

and 'eq method_desc =
  { ma_name: method_name; (* name of the method *)
    ma_input: (Ident.t * Deftypes.typ) list; (* list of input arguments *)
    ma_output: Ident.t * Deftypes.typ;
    ma_env: ventry Ident.Env.t; (* local environment *)
    ma_body: 'eq }

and ventry =
  { v_ty: Deftypes.typ;
    v_value: exp option }

and mentry =
  { m_ty: Deftypes.typ;
    m_value: exp option;
    m_kind: mem }

and ientry =
  { i_machine: Lident.t;
    i_kind: Deftypes.kind }

and method_name = 
  | Ostep (* computes values and possible changes of states *)
  | Oreset (* resets the discrete state *)
  | Oderivatives (* computes the values of derivatives *)
  | Ocrossings (* computes the zero-crossing functions *)
  | Omaxsize (* returns the size of the cvector and zvector *)
  | Oreinit (* should we re-init the solver? *)
  | Ocin | Ocout (* copies the continuous state vector *)
  | Odout | Oczin | Oclear_zin | Oczout
                 (* copies derivatives and zero crossings *)
  | Ocsize | Ozsize (* current size for cont. states and zero crossings *)

and 'eq implementation =
    | Oletvalue of string * exp
    | Oletfun of string * Ident.t list * exp
    | Oletmachine of string * 'eq machine
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
