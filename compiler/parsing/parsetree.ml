(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* Abstract syntax tree after parsing *)

open Location

type kind = A | C | AD | D
type name = string

type qualident = { qual: name; id: name }
type longname =
    | Name of name
    | Modname of qualident

type 'a localized = { desc: 'a; loc: Location.location }


(** Types *)
type type_expression = type_expression_desc localized 

and type_expression_desc =
    | Etypevar of string
    | Etypeconstr of longname * type_expression list
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
    | Efundecl of name * kind * is_atomic * pattern list * exp

and type_signature =
    { sig_inputs : type_expression list;
      sig_output : type_expression;
      sig_kind : kind;
      sig_safe : bool }

and is_atomic = bool

and exp = desc localized

and desc =
  | Evar of longname
  | Econst of immediate
  | Econstr0 of constr
  | Elast of name
  | Eapp of op * exp list
  | Etuple of exp list
  | Erecord_access of exp * longname
  | Erecord of (longname * exp) list
  | Etypeconstraint of exp * type_expression
  | Elet of is_rec * eq list * exp
  | Eseq of exp * exp
  | Eperiod of period
  | Ematch of exp * exp match_handler list
  | Epresent of exp present_handler list * exp option
  | Eautomaton of exp state_handler list * state_exp option
  | Ereset of exp * exp

and is_rec = bool

and op =
    | Efby | Eunarypre | Eifthenelse | Eminusgreater | Eup | Einitial | Edisc | Eon
    | Etest | Eop of longname

and immediate =
    | Eint of int
    | Efloat of float
    | Ebool of bool
    | Echar of char
    | Estring of string
    | Evoid

(* a period is of the form v^* (v^+). E.g., 0.2 (3.4 5.2) *)
and period =
    { p_phase: float list;
      p_period: float list }

and constr = longname

and pattern = pdesc localized

and pdesc =
  | Etuplepat of pattern list
  | Evarpat of name
  | Ewildpat
  | Econstpat of immediate
  | Econstr0pat of longname
  | Ealiaspat of pattern * name
  | Eorpat of pattern * pattern
  | Erecordpat of (longname * pattern) list
  | Etypeconstraintpat of pattern * type_expression

and eq = eqdesc localized

and eqdesc =
  | EQeq of pattern * exp
    (* [p = e] *)
  | EQder of name * exp * exp option * exp present_handler list
    (* [der n = e [init e0] [reset p1 -> e1 | ... | pn -> en]] *)
  | EQinit of pattern * exp * exp option
    (* [init p = e0] or [p = e init e0] *)
  | EQnext of pattern * exp * exp option
    (* [next p = e] or [next p = e init e0] *) 
  | EQemit of name * exp option
    (* [emit n = e] *)
  | EQautomaton of eq list state_handler list * state_exp option
  | EQpresent of eq list block present_handler list * eq list block option
  | EQmatch of exp * eq list block match_handler list
  | EQreset of eq list * exp

and 'a block = 'a block_desc localized

and 'a block_desc = 
    { b_vars: name list;
      b_locals: local list;
      b_body: 'a } 

and local = local_desc localized

and local_desc = is_rec * eq list 

and statepat = statepatdesc localized 

and statepatdesc = 
    | Estate0pat of name 
    | Estate1pat of name * pattern list

and state_exp = state_exp_desc localized 

and state_exp_desc = 
    | Estate0 of name 
    | Estate1 of name * exp list

and escape = 
    { e_cond: scondpat; (* condition to escape *)
      e_reset: bool; (* is-it a reset or not *)
      e_block: eq list block option; (* values emited on the transition *)
      e_next_state: state_exp; (* next active state *) } 

and scondpat = scondpat_desc localized

and scondpat_desc =
    | Econdand of scondpat * scondpat
    | Econdor of scondpat * scondpat
    | Econdexp of exp
    | Econdon of scondpat * exp
    | Econdpat of exp * pattern

and is_on = bool

and 'a match_handler =
    { m_pat: pattern;
      m_body: 'a; }

and 'a present_handler =
    { p_cond: scondpat;
      p_body: 'a; }

and 'a state_handler = 
    { s_state : statepat; 
      s_block : 'a block; 
      s_until : escape list; 
      s_unless : escape list; } 
