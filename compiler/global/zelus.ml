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

(* Abstract syntax tree after scoping *)

open Location
open Misc

type kind = S | A | C | D | AD | AS | P
type name = string

type 'a localized = { desc: 'a; loc: Location.location }


(** Types *)
type type_expression = type_expression_desc localized 

and type_expression_desc =
  | Etypevar of string
  | Etypeconstr of Lident.t * type_expression list
  | Etypetuple of type_expression list
  | Etypevec of type_expression * size
  | Etypefun of kind * Ident.t option * type_expression * type_expression

and size = size_desc localized

and size_desc =
  | Sconst of int
  | Sglobal of Lident.t
  | Sname of Ident.t
  | Sop of size_op * size * size

and size_op = Splus | Sminus
		   
(** Declarations and expressions *)
type interface = interface_desc localized

and interface_desc =
  | Einter_open of name
  | Einter_typedecl of name * name list * type_decl
  | Einter_constdecl of name * type_expression

and type_decl = type_decl_desc localized
    
and type_decl_desc =
  | Eabstract_type
  | Eabbrev of type_expression
  | Evariant_type of constr_decl list
  | Erecord_type of (name * type_expression) list
					     
and constr_decl = constr_decl_desc localized

and constr_decl_desc =
  | Econstr0decl of name
  | Econstr1decl of name * type_expression list

and implementation = implementation_desc localized

and implementation_desc =
  | Eopen of name
  | Etypedecl of name * name list * type_decl
  | Econstdecl of name * is_static * exp
  | Efundecl of name * funexp
			 
and funexp =
  { f_kind: kind;
    f_atomic: is_atomic;
    f_args: pattern list;
    f_body: exp;
    mutable f_env: Deftypes.tentry Ident.Env.t;
    f_loc: location }
    
and is_atomic = bool

and is_static = bool
		  
and exp = 
  { mutable e_desc: desc; (* descriptor *)
    e_loc: location; (* location in the source code *)
    mutable e_typ: Deftypes.typ; (* its type *)
    mutable e_caus: Defcaus.tc; (* its causality type *)
    mutable e_init: Definit.ti; (* its initialization type *)
  }
    
and desc =
  | Elocal of Ident.t
  | Eglobal of { lname : Lident.t; typ_instance : Deftypes.typ_instance }
  | Econst of immediate
  | Econstr0 of Lident.t
  | Econstr1 of Lident.t * exp list
  | Elast of Ident.t
  | Eapp of app * exp * exp list
  | Eop of op * exp list
  | Etuple of exp list
  | Erecord_access of exp * Lident.t
  | Erecord of (Lident.t * exp) list
  | Erecord_with of exp * (Lident.t * exp) list
  | Etypeconstraint of exp * type_expression
  | Epresent of exp present_handler list * exp option
  | Ematch of total ref * exp * exp match_handler list
  | Elet of local * exp
  | Eseq of exp * exp
  | Eperiod of exp period
  | Eblock of eq list block * exp

and is_rec = bool

and op =
  | Efby | Eunarypre (* unit delay *)
  | Eifthenelse (* mux *)
  | Eminusgreater (* initialization *)
  | Eup (* zero-crossing detection *)
  | Einitial (* true at the very first instant *)
  | Edisc (* discontinuity of a flow *)
  | Ehorizon (* generate an event at a given horizon *)
  | Etest (* test the present of a signal *)
  | Eaccess (* access in an array: e.(e2) *)
  | Eupdate (* array update: [| e1 with i = e2 |] *)
  | Eslice of size * size (* array slice: e{s0..s1} *)
  | Econcat (* array concatenation: [| t{0..42} | t'{2..25} |] *)
  | Eatomic (* force its argument to be atomic *)
    
and immediate = Deftypes.immediate

and app = { app_inline: bool; app_statefull: bool}
				    
(* a period is of the form period(v1) or period(v1|v2) where v1 is the phase *)
(* v1 and v2 two static expressions. v1 and v2 of type float. *)
(* E.g., period (0.2|3.4) *)
and 'a period =
  { p_phase: 'a option; (* the two expressions must be static *)
    p_period: 'a }

and pattern =
  { mutable p_desc: pdesc; (* its descriptor *)
    p_loc: location; (* where it is in the source code *)
    mutable p_typ: Deftypes.typ; (* its type *)
    mutable p_caus: Defcaus.tc; (* its causality type *)
    mutable p_init: Definit.ti; (* its initialization type *)
  }

and pdesc =
  | Ewildpat
  | Econstpat of immediate
  | Econstr0pat of Lident.t
  | Econstr1pat of Lident.t * pattern list
  | Etuplepat of pattern list
  | Evarpat of Ident.t
  | Ealiaspat of pattern * Ident.t
  | Eorpat of pattern * pattern
  | Erecordpat of (Lident.t * pattern) list
  | Etypeconstraintpat of pattern * type_expression

and eq = 
  { eq_desc: eqdesc; (* its descriptor *)
    eq_loc: location; (* its location in the source file *)
    eq_index: int; (* a unique index; used to build a partial order *)
    eq_safe: bool; (* does it have a side effect *)
    mutable eq_write: Deftypes.defnames; (* the set of names it defines *) }

and eqdesc =
  | EQeq of pattern * exp
  (* [p = e] *)
  | EQder of Ident.t * exp * exp option * exp present_handler list
  (* [der n = e [init e0] [reset p1 -> e1 | ... | pn -> en]] *)
  | EQinit of Ident.t * exp
  (* [init n = e0 *)
  | EQnext of Ident.t * exp * exp option
  (* [next n = e] *)
  | EQpluseq of Ident.t * exp
  (* [n += e] *)
  | EQautomaton of is_weak * state_handler list * state_exp option
  | EQpresent of eq list block present_handler list * eq list block option
  | EQmatch of total ref * exp * eq list block match_handler list
  | EQreset of eq list * exp
  | EQemit of Ident.t * exp option
  | EQblock of eq list block
  | EQand of eq list (* eq1 and ... and eqn *)
  | EQbefore of eq list (* eq1 before ... before eqn *)
  | EQforall of forall_handler (* forall i in ... do ... initialize ... done *)

and total = bool

and is_next = bool

and is_weak = bool

and 'a block =
    { b_vars: vardec list;
      b_locals: local list;
      b_body: 'a;
      b_loc: location;
      mutable b_env: Deftypes.tentry Ident.Env.t;
      mutable b_write: Deftypes.defnames }

and vardec =
    { vardec_name: Ident.t; (* its name *)
      vardec_default: Deftypes.constant default option;
      (* either an initial or a default value *)
      vardec_combine: Lident.t option; (* an optional combination function *)
      vardec_loc: location;
    }

and 'a default =
  | Init of 'a | Default of 'a


and local = 
  { l_rec: is_rec; (* is-it recursive *)
    l_eq: eq list; (* the set of parallel equations *)
    mutable l_env: Deftypes.tentry Ident.Env.t;
    l_loc: location }

and state_handler = 
    { s_loc: location;
      s_state: statepat; 
      s_body: eq list block; 
      s_trans: escape list;
      mutable s_env: Deftypes.tentry Ident.Env.t;
      mutable s_reset: bool } 

and statepat = statepatdesc localized 

and statepatdesc = 
    | Estate0pat of Ident.t 
    | Estate1pat of Ident.t * Ident.t list

and state_exp = state_exdesc localized 

and state_exdesc = 
    | Estate0 of Ident.t
    | Estate1 of Ident.t * exp list

and escape = 
    { e_cond: scondpat; 
      e_reset: bool; 
      e_block: eq list block option;
      e_next_state: state_exp;
      mutable e_env: Deftypes.tentry Ident.Env.t;
      mutable e_zero: bool } 

and scondpat = scondpat_desc localized

and scondpat_desc =
    | Econdand of scondpat * scondpat
    | Econdor of scondpat * scondpat
    | Econdexp of exp
    | Econdpat of exp * pattern
    | Econdon of scondpat * exp

and 'a match_handler =
    { m_pat: pattern;
      m_body: 'a;
      mutable m_env: Deftypes.tentry Ident.Env.t;
      m_reset: bool; (* the handler is reset on entry *)
      mutable m_zero: bool; (* the handler is done at a zero-crossing instant *)
    }

(* the body of a present handler *)
and 'a present_handler =
    { p_cond: scondpat;
      p_body: 'a;
      mutable p_env: Deftypes.tentry Ident.Env.t;
      mutable p_zero: bool }

(* the body of a for loop *)
(* for(all|seq) [id in e..e | id in e[at id] | id out id]+
 *   local id [and id]*
 *   do eq and ... and eq
 *   [init
 *     [[id = e with g] | [last id = e]]
 *     [and [[id = e with g] | [last id = e]]]*
 *   done *)
and forall_handler =
  { for_index: indexes_desc localized list;
    for_init: init_desc localized list;
    for_body: eq list block;
    mutable for_in_env: Deftypes.tentry Ident.Env.t;
    (* def names from [id in e | id in e1..e2] *)
    mutable for_out_env: Deftypes.tentry Ident.Env.t;
    (* def (left) names from [id out id'] *)
    for_loc: location }

and indexes_desc =
  | Einput of Ident.t * exp (* xi in t_input *)
  | Eoutput of Ident.t * Ident.t (* xi out t_output *)
  | Eindex of Ident.t * exp * exp (* i in e1 .. e2 *)

and init_desc =
  | Einit_last of Ident.t * exp

					 

