(* Abstract syntax tree after scoping *)

open Location
open Misc

type kind = A | C | D
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
      mutable e_typ: Deftypes.typ }

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
  | Elet of local * exp
  | Eseq of exp * exp
  | Eperiod of period

and op =
    | Efby | Eunarypre | Eifthenelse 
    | Eminusgreater | Eup | Einitial | Edisc
    | Etest | Eon | Eop of Lident.t

and immediate = Deftypes.immediate

(* a period is an expression of the form v^* (v^+). E.g., 0.2 (3.4 5.2) *)
and period =
    { p_phase: float list;
      p_period: float list }

and pattern =
    { mutable p_desc: pdesc;
      p_loc: location;
      mutable p_typ: Deftypes.typ }

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
      eq_loc: location }

and eqdesc =
  | Eeq of pattern * exp
  | Eder of Ident.t * exp * exp option * (exp * exp) list
  | Eactivate of pattern * (exp * exp) list * exp option * exp option
  | Einit of pattern * exp
  | Eautomaton of state_handler list * state_exp option
  | Epresent of present_handler list * block option
  | Ematch of total ref * exp * match_handler list
  | Ereset of block * exp
  | Eemit of Ident.t * exp option
 
and total = bool

and block =
    { b_vars: Ident.t list;
      b_locals: local list;
      b_eq: eq list;
      b_loc: location;
      b_env: Deftypes.tentry Ident.Env.t;
      mutable b_write: Ident.S.t }

and local = 
    { l_eq: eq list;
      l_env: Deftypes.tentry Ident.Env.t;
      l_loc: location }

and state_handler = 
    { s_state: statepat; 
      s_block: block; 
      s_until: escape list; 
      s_unless: escape list;
      s_env: Deftypes.tentry Ident.Env.t;
      mutable s_reset: bool } 

and statepat = statepatdesc localized 

and statepatdesc = 
    | Estate0pat of Ident.t 
    | Estate1pat of Ident.t * pattern list

and state_exp = state_exdesc localized 

and state_exdesc = 
    | Estate0 of Ident.t
    | Estate1 of Ident.t * exp list

and escape = 
    { e_cond: scondpat; 
      e_reset: bool; 
      e_block: block option;
      e_next_state: state_exp;
      e_env: Deftypes.tentry Ident.Env.t } 

and scondpat = scondpat_desc localized

and scondpat_desc =
    | Econdand of is_on * scondpat * scondpat
    | Econdexp of exp
    | Econdpat of exp * pattern

and is_on = bool

and match_handler =
    { m_pat: pattern;
      m_block: block;
      m_env: Deftypes.tentry Ident.Env.t;
      m_reset: bool }

and present_handler =
    { p_cond: scondpat;
      p_block: block;
      p_env: Deftypes.tentry Ident.Env.t }

let desc e = e.desc
let make x = { desc = x; loc = no_location }
