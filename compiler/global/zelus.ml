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
(* Abstract syntax tree after scoping *)

open Location
open Misc

type kind = A | C | D | AD
type name = string

type 'a localized = { desc: 'a; loc: Location.location }


(** Types *)
type type_expression = type_expression_desc localized 

and type_expression_desc =
    | Etypevar of string
    | Etypeconstr of Lident.t * type_expression list
    | Etypetuple of type_expression list

(** Declarations and expressions *)
type interface = interface_desc localized

and interface_desc =
    | Einter_open of name
    | Einter_typedecl of name * name list * type_decl
    | Einter_constdecl of name * type_expression
    | Einter_fundecl of name * type_signature

and type_decl =
    | Eabstract_type
    | Eabbrev of type_expression
    | Evariant_type of name list
    | Erecord_type of (name * type_expression) list

and implementation = implementation_desc localized

and implementation_desc =
    | Eopen of name
    | Etypedecl of name * name list * type_decl
    | Econstdecl of name * exp
    | Efundecl of name * funexp

and funexp =
    { f_kind: kind;
      f_atomic: bool;
      f_args: pattern list;
      f_body: exp;
      f_env: Deftypes.tentry Ident.Env.t }

and type_signature =
    { sig_inputs: type_expression list;
      sig_output: type_expression;
      sig_kind: kind;
      sig_safe: bool }

and exp = 
    { mutable e_desc: desc;
      e_loc: location;
      mutable e_typ: Deftypes.typ;
      mutable e_caus: Defcaus.t list }

and desc =
  | Elocal of Ident.t
  | Eglobal of Lident.t
  | Econst of immediate
  | Econstr0 of Lident.t
  | Elast of Ident.t
  | Eapp of op * exp list
  | Etuple of exp list
  | Erecord_access of exp * Lident.t
  | Erecord of (Lident.t * exp) list
  | Etypeconstraint of exp * type_expression
  | Epresent of exp present_handler list * exp option
  | Ematch of total ref * exp * exp match_handler list
  | Elet of local * exp
  | Eseq of exp * exp
  | Eperiod of period

and op =
  | Efby | Eunarypre | Eifthenelse 
  | Eminusgreater | Eup | Einitial | Edisc | Ehorizon | Eafter
  | Etest
  | Eop of is_inline * Lident.t
  | Eevery of is_inline * Lident.t

and immediate = Deftypes.immediate

and is_inline = bool

(* a period is an expression of the form [v] (v). E.g., 0.2 (3.4) or (4.5) *)
and period =
    { p_phase: float option;
      p_period: float }

and pattern =
    { mutable p_desc: pdesc;
      p_loc: location;
      mutable p_typ: Deftypes.typ;
      mutable p_caus: Defcaus.t list }

and pdesc =
  | Ewildpat
  | Econstpat of immediate
  | Econstr0pat of Lident.t
  | Etuplepat of pattern list
  | Evarpat of Ident.t
  | Ealiaspat of pattern * Ident.t
  | Eorpat of pattern * pattern
  | Erecordpat of (Lident.t * pattern) list
  | Etypeconstraintpat of pattern * type_expression

and eq = 
    { eq_desc: eqdesc;
      eq_loc: location;
      mutable eq_write: Deftypes.defnames }

and eqdesc =
  | EQeq of pattern * exp
  (* [p = e] *)
  | EQder of Ident.t * exp * exp option * exp present_handler list
  (* [der n = e [init e0] [reset p1 -> e1 | ... | pn -> en]] *)
  | EQinit of Ident.t * exp
  (* [init n = e0 *)
  | EQnext of Ident.t * exp * exp option
  (* [next n = e] *)
  | EQset of Lident.t * exp
  (* [n <- e] *)
  | EQautomaton of is_weak * state_handler list * state_exp option
  | EQpresent of eq list block present_handler list * eq list block option
  | EQmatch of total ref * exp * eq list block match_handler list
  | EQreset of eq list * exp
  | EQemit of Ident.t * exp option
  | EQblock of eq list block

and total = bool

and is_next = bool

and is_weak = bool

and 'a block =
    { b_vars: Ident.t list;
      b_locals: local list;
      b_body: 'a;
      b_loc: location;
      b_env: Deftypes.tentry Ident.Env.t;
      mutable b_write: Deftypes.defnames }

and local = 
    { l_eq: eq list;
      l_env: Deftypes.tentry Ident.Env.t;
      l_loc: location }

and state_handler = 
    { s_loc: location;
      s_state: statepat; 
      s_body: eq list block; 
      s_trans: escape list;
      s_env: Deftypes.tentry Ident.Env.t;
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
      e_env: Deftypes.tentry Ident.Env.t;
      mutable e_zero: bool } 

and scondpat = scondpat_desc localized

and scondpat_desc =
    | Econdand of scondpat * scondpat
    | Econdor of scondpat * scondpat
    | Econdexp of exp
    | Econdpat of exp * pattern
    | Econdon of scondpat * exp

and is_on = bool

and 'a match_handler =
    { m_pat: pattern;
      m_body: 'a;
      m_env: Deftypes.tentry Ident.Env.t;
      m_reset: bool; (* the handler is reset on entry *)
      mutable m_zero: bool; (* the handler is done at a zero-crossing instant *)
    }

and 'a present_handler =
    { p_cond: scondpat;
      p_body: 'a;
      p_env: Deftypes.tentry Ident.Env.t;
      mutable p_zero: bool }
