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

(* abstract syntax tree of the object code *)

open Location
open Misc
open Ident

type name = string

(* a continuous state variable [x] is a pair *)
(* with two fields: [x.der] for its derivative. [x.pos] *)
(* for its current value. *)
(* a zero-crossing variable [x] has two field: [x.zin] is true when *)
(* the solver has detected a zero-crossing. [x.zout] is the value *)
(* to be observed for a zero-crossing *)

(* expressions are expected to be safe; unsafe ones must be put *)
(* into instructions *)
type exp = 
  | Oconst of immediate (* immediate constant *)
  | Oconstr0 of Lident.t (* 0-ary and 1-ary constructor *)
  | Oconstr1 of Lident.t * exp list
  | Oglobal of Lident.t (* global variable *)
  | Olocal of Ident.t (* read of local value *)
  | Ovar of is_mutable * Ident.t (* read of local variable *)
  | Ostate of left_state_value (* read of a state variable *)
  | Oaccess of exp * exp (* access in an array *)
  | Oupdate of size * exp * exp * exp (* update of an array of size [s1] *)
  | Oslice of exp * size * size (* e{s1..s2} *)
  | Oconcat of exp * size * exp * size (* { e1 | e2 } *)
  | Ovec of exp * size (* e1[e2] build an array of size [s2] with value [e1] *)
  | Otuple of exp list (* tuples *)
  | Oapp of exp * exp list (* function application *)
  | Orecord of (Lident.t * exp) list (* record *)
  | Orecord_access of exp * Lident.t (* access to a record field *)
  | Orecord_with of exp * (Lident.t * exp) list (* record with copy *)
  | Otypeconstraint of exp * type_expression (* type constraint *)
  | Oifthenelse of exp * exp * exp
  | Omethodcall of method_call			       
  | Oinst of inst
                          
 (* when [is_mutable = true] a variable [x] is mutable which means that *)
 (* x <- ... and ...x... are valid expression; otherwise a ref will be *)
 (* added when translated into OCaml **)
 and is_mutable = bool
                    
 (* instructions *)
and inst =
  | Olet of pattern * exp * inst
  | Oletvar of Ident.t * is_mutable * Deftypes.typ * exp option * inst
  | Ofor of bool * Ident.t * exp * exp * inst
  | Owhile of exp * inst
  | Omatch of exp * inst match_handler list
  | Oif of exp * inst * inst option
  | Oassign of left_value * exp
  | Oassign_state of left_state_value * exp
  | Osequence of inst list
  | Oexp of exp		     

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
  | Oany
      
and pattern = 
  | Owildpat
  | Otuplepat of pattern list
  | Ovarpat of Ident.t * type_expression
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
  { ma_kind: Deftypes.kind; (* combinatorial, continuous-time or discrete-time *)
    ma_params: pattern list; (* list of static parameters *)
    ma_initialize: inst option;
                             (* code to execute at the creation of the machine *)
    ma_memories: mentry list;(* memories *)
    ma_instances: ientry list; (* instances *)
    ma_methods: method_desc list; (* methods *) 
  }

and mentry =
  { m_name: Ident.t; (* its name *)
    m_value: exp option; (* its possible initial value *)
    m_typ: Deftypes.typ; (* its type *)
    m_kind: Deftypes.mkind option; (* the kind of the memory *)
    m_size: exp path; (* it may be an array *)
  }

and ientry =
  { i_name: Ident.t; (* its name *)
    i_machine: exp;  (* the machine it belongs to *)
    i_kind: Deftypes.kind; (* the kind of the machine *)
    i_params: exp path; (* static parameters used at instance creation *)
    i_size: exp list; (* it is possibly an array of instances *)
  }
    
and method_desc =
  { me_name: method_name; (* name of the method *)
    me_params: pattern list; (* list of input arguments *)
    me_body: inst; (* body *)
    me_typ: Deftypes.typ; (* type of the result *)
  }

and method_call =
  { met_machine: Lident.t option; (* the class of the method *)
    met_name: method_name; (* the name of the method *)
    met_instance: (Ident.t * exp path) option;
    (* either a call to self (None) or to *)
    (* one instance o.(index_1)...(index_n).m(e_1,...,e_k) *)
    met_args: exp list }

and method_name = name
		    
and 'a path = 'a list
                 
and implementation_list = implementation list

and implementation = 
  | Oletvalue of name * inst
  | Oletfun of name * pattern list * inst
  | Oletmachine of name * machine
  | Oopen of string
  | Otypedecl of (string * string list * type_decl) list

(* type declaration *)
and type_expression = 
  | Otypevar of string
  | Otypefun of kind * Ident.t option * type_expression * type_expression
  | Otypetuple of type_expression list
  | Otypeconstr of Lident.t * type_expression list
  | Otypevec of type_expression * size

and size =
  | Sconst of int
  | Sname of Ident.t
  | Sglobal of Lident.t
  | Sop of size_op * size * size
      
and size_op = Splus | Sminus

and kind = Ofun | Onode 

and type_decl =
  | Oabstract_type
  | Oabbrev of type_expression
  | Ovariant_type of constr_decl list
  | Orecord_type of (string * type_expression) list
					       
and constr_decl =
  | Oconstr0decl of string
  | Oconstr1decl of string * type_expression list
					     
