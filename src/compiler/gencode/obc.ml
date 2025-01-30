(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* abstract syntax tree of the object code *)

type name = string

type 'a record = { label: Lident.t; arg: 'a }

type ('pattern, 'body) match_handler =
  { m_pat : 'pattern;
    m_body: 'body;
  }

(* type declaration *)
type type_expression = Zelus.type_expression

type kind = Efun | Enode

type size_expression = Zelus.size_expression

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
  | Evarpat of { id: Ident.t; ty: type_expression }
  | Econstpat of immediate
  | Ealiaspat of pattern * Ident.t
  | Econstr0pat of Lident.t
  | Econstr1pat of Lident.t * pattern list
  | Eorpat of pattern * pattern
  | Erecordpat of pattern record list
  | Etypeconstraintpat of pattern * type_expression

(* a continuous state variable [x] is a pair *)
(* with two fields: [x.der] for its derivative. [x.pos] *)
(* for its current value. *)
(* a zero-crossing variable [x] has two field: [x.zin] is true when *)
(* the solver has detected a zero-crossing. [x.zout] is the value *)
(* to be observed for a zero-crossing *)

(* expressions are expected to be safe; unsafe ones must be put *)
(* into instructions *)
and exp = 
  | Econst of immediate (* immediate constant *)
  | Econstr0 of { lname: Lident.t } (* 0-ary and 1-ary constructor *)
  | Econstr1 of { lname : Lident.t; arg_list : exp list }
  | Eglobal of { lname : Lident.t } (* global variable *)
  | Evar of { is_mutable: is_mutable; id : Ident.t }
  (* read of local value - shared (reference) or not *)
  | Estate of left_state_value (* read of a state variable *)
  | Etuple of exp list
  | Erecord of exp record list
  | Erecord_access of exp record
  | Erecord_with of exp * exp record list
  | Eifthenelse of exp * exp * exp
  | Ematch of exp * (pattern, exp) match_handler list
  | Elet of pattern * exp * exp (* [let p = e1 in e2] *)
  | Eletvar of { id: Ident.t; is_mutable: is_mutable;
                 ty: Deftypes.typ; e_opt: exp option; e : exp }
  (* var id : ty [= e1] in e2 *)
  | Eletmem of mentry list * exp (* [let mem m1...mk in e] *)
  | Eletinstance of ientry list * exp (* [let instances i1...ik in e] *)
  | Eassign of left_value * exp (* [x.v <- ...] *)
  | Eassign_state of left_state_value * exp (* [x.v <- ...] *)
  | Esequence of exp list
  | Eapp of { f: exp; arg_list: exp list }
  | Emethodcall of methodcall
  | Etypeconstraint of exp * Zelus.type_expression
  | Efor of { index: Ident.t; dir: bool; left: exp; right: exp; e: exp }
  | Ewhile of { cond: exp; e: exp }
  | Eassert of exp
  | Emachine of machine
  | Efun of { pat_list: pattern list; e: exp }
  (* array operations *)
  | Eget of { e: exp; index: exp } (* access in an array *)
  | Eupdate of { e: exp; size: exp; index: exp; arg: exp }
  (* update of an array [e1] of size [s1] [|e1 with (i) <- e2|]*)
  | Eslice of
      { e: exp; left: exp; right: exp } (* e{s1..s2} *)
  | Econcat of { left: exp; left_size: exp;
                 right: exp; right_size: exp }
  (* { e1 ++ e2 } *)
  | Evec of { e: exp; size: exp }
  (* e1[e2] build an array of size [s2] with value [e1] *)
               
(* when [is_mutable = true] a variable [x] is mutable which means that *)
(* x <- ... and ...x... are valid expression; otherwise a ref will be *)
(* added when translated into OCaml **)
and is_mutable = bool

and left_value = 
  | Eleft_name of Ident.t
  | Eleft_record_access of left_value record
  | Eleft_index of left_value * exp
  
and left_state_value =
  | Eself
  | Eleft_state_global of Lident.t 
  | Eleft_instance_name of Ident.t
  | Eleft_state_name of Ident.t
  | Eleft_state_record_access of left_state_value record
  | Eleft_state_index of left_state_value * exp
  | Eleft_state_primitive_access of left_state_value * primitive_access

(* a machine provides certain fields for reading/writting state variables *)
and primitive_access =
  | Eder (* x.der.(i) <- ... *)
  | Epos (* x.pos.(i) <- ... *)
  | Ezero_out (* x.zero_out.(i) <-... *)
  | Ezero_in (* ... x.zero_in.(i) ... *)

(* Definition of a sequential machine *)
and machine =
  { ma_name: Ident.t; (* name of the machine *)
    ma_kind: Deftypes.kind;
    (* combinatorial, continuous-time or discrete-time *)
    ma_initialize: exp option;
    ma_params: pattern list; (* list of static parameters *)
    ma_memories: mentry list;(* its memories *)
    ma_instances: ientry list; (* its node instances *)
    ma_methods: method_desc list; (* its methods *) 
  }

and mentry =
  { m_name: Ident.t; (* its name *)
    m_value: exp option; (* its initial value *)
    m_typ: Deftypes.typ; (* its type *)
    m_kind: Deftypes.mkind option; (* the kind of the memory *)
    m_size: exp path; (* it may be an array *)
  }

and ientry =
  { i_name: Ident.t; (* its name *)
    i_machine: exp;  (* the machine it belongs to *)
    i_kind: Deftypes.kind;  (* the kind of the machine *)
    i_params: exp path; (* static parameters used at instance creation *)
    i_size: exp list; (* it is possibly an array of instances *)
  }
    
and method_desc =
  { me_name: method_name; (* name of the method *)
    me_params: pattern list; (* list of input arguments *)
    me_body: exp; (* its result *)
    me_typ: Deftypes.typ; (* type of the result *)
  }

and methodcall =
  { met_machine: Lident.t option; (* the class of the method *)
    met_name: method_name; (* name of the method *)
    met_instance: (Ident.t * exp path) option;
    (* either a call to self (None) or to *)
    (* one instance o.(index_1)...(index_n).m(e_1,...,e_k) *)
    met_args: exp list;
  }

and method_name = name

(* The different kinds of state variables *)
and mkind =
  | Econt (* continuous state variable *)
  | Ezero (* zero-crossing *)
  | Ehorizon (* horizon *)
  | Emajor (* true in discrete mode; major step *)
  | Eencore (* a cascade event *)
  | Eperiod (* a event defined by a period *)
        
and 'a path = 'a list

type type_decl =
  | Eabstract_type
  | Eabbrev of Zelus.type_expression 
  | Evariant_type of constr_decl list 
  | Erecord_type of (is_mutable * name * Zelus.type_expression) list

and constr_decl =
  | Econstr0decl of name 
  | Econstr1decl of name * Zelus.type_expression list

type implementation = 
  (* [let x1,...xn = e]; when n = 0, it means [let () = e]  *)
  | Eletdef of (name list * exp) list 
  | Eopen of name
  | Etypedecl of (name * name list * type_decl) list

type program =
  { p_impl_list: implementation list }
    [@@deriving show]
