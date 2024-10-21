(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

type 'a localized = { desc: 'a; loc: Location.t }

type name = String.t

type kind =
  | Knode : tkind -> kind (* stateful *)
  | Kfun : vkind -> kind (* combinatorial *)

and vkind =
  | Kconst (* constant; known at compilation time *)
  | Kstatic (* constant; known at instantiation time *)
  | Kany (* known dynamically *)

and tkind =
  | Kdiscrete (* only discrete-time state variables *)
  | Kcont (* discrete-time and continuous-time state variables *)

type longname =
  | Name : name -> longname
  | Modname : qualident -> longname

and qualident = { qual: name; id: name }

(** Types *)
type type_expression = type_expression_desc localized

and type_expression_desc =
  | Etypevar : name -> type_expression_desc
  | Etypeconstr : longname * type_expression list -> type_expression_desc
  | Etypetuple : type_expression list -> type_expression_desc
  | Etypefun : kind * name option * type_expression * type_expression ->
               type_expression_desc
  | Etypevec : type_expression * size -> type_expression_desc

and size = size_desc localized

and size_desc =
  | Size_int of int
  | Size_var of name
  | Size_frac of size * int
  | Size_op of op * size * size

and op = Size_plus | Size_minus | Size_mult

(* constants *)
type immediate =
| Eint : int -> immediate
| Ebool : bool -> immediate
| Efloat : float -> immediate
| Echar : char -> immediate
| Estring : string -> immediate
| Evoid : immediate

(* synchronous and array operators *)
type operator =
  | Efby : operator
  (* unit delay *)
  | Eifthenelse : operator
  (* mux *)
  | Eminusgreater : operator
  (* initialization *)
  | Eunarypre : operator
  (* unit delay *)
  | Eseq : operator
  (* instantaneous sequence *)
  | Erun : is_inline -> operator
  (* mark that a function is a node (statefull) *)
  | Eatomic : operator
  (* force its argument to be atomic *)
  | Etest : operator
  (* test the present of a signal *)
  | Eup : operator
  (* zero-crossing detection *)
  | Eperiod : operator
  (* period *)
  | Ehorizon : operator
  (* generate an event at a given horizon *)
  | Edisc : operator
  (* generate an event whenever x <> last x outside of integration *)
  | Earray : array_operator -> operator

and array_operator =
  | Earray_list : array_operator
  (* [| e1;...;en |] *)
  | Econcat : array_operator
  (* [e1 ++ e2] *)
  | Eget : array_operator
  (* [e.(e)] *)
  | Eget_with_default : array_operator
  (* [e.(e) default e] *)
  | Eslice : array_operator
  (* [e.(e..e)] *)
  | Eupdate : array_operator
  (* [| e with (e1,...,en) <- e |] *)
  | Etranspose : array_operator
  (* [transpose e] *)
  | Eflatten : array_operator
  (* [flatten e] *)
  | Ereverse : array_operator
  (* [reverse e] *)

and is_inline = bool

type pateq = pateq_desc localized

and pateq_desc = name list

(* declaration of a local variable [x [init e1] [default e2]] *)
type 'exp vardec_desc =
  { var_name: name;
    var_default: 'exp option;
    var_init: 'exp option;
    var_clock: bool;
    var_is_last: bool;
    var_typeconstraint: type_expression option;
  }

and 'exp vardec = 'exp vardec_desc localized

type ('exp, 'body) block = ('exp, 'body) block_desc localized

and ('exp, 'body) block_desc =
    { b_vars: 'exp vardec list;
      b_body: 'body }

type pattern = pattern_desc localized

and pattern_desc =
  | Etuplepat : pattern list -> pattern_desc
  | Evarpat : name -> pattern_desc
  | Ewildpat : pattern_desc
  | Econstpat : immediate -> pattern_desc
  | Econstr0pat : longname -> pattern_desc
  | Econstr1pat : longname * pattern list -> pattern_desc
  | Ealiaspat : pattern * name -> pattern_desc
  | Eorpat : pattern * pattern -> pattern_desc
  | Erecordpat : (longname * pattern) list -> pattern_desc
  | Etypeconstraintpat : pattern * type_expression -> pattern_desc

type statepatdesc =
  | Estate0pat : name -> statepatdesc
  | Estate1pat : name * name list -> statepatdesc

type statepat = statepatdesc localized

type 'exp state_desc =
  | Estate0 : name -> 'exp state_desc
  | Estate1 : name * 'exp list -> 'exp state_desc
  | Estateif : 'exp * 'exp state * 'exp state -> 'exp state_desc

and 'exp state = 'exp state_desc localized

type ('exp, 'body) match_handler_desc =
  { m_pat : pattern;
    m_body: 'body;
  }

and ('exp, 'body) match_handler = ('exp, 'body) match_handler_desc localized

type ('scondpat, 'body) present_handler_desc =
  { p_cond: 'scondpat;
    p_body: 'body; }

and ('scondpat, 'body) present_handler =
  ('scondpat, 'body) present_handler_desc localized

type is_weak = bool

type exp = exp_desc localized

and exp_desc =
  | Econst : immediate -> exp_desc
  | Econstr0 : longname -> exp_desc
  | Econstr1 : longname * exp list -> exp_desc
  | Evar : longname -> exp_desc
  | Elast : is_copy * name -> exp_desc
  | Eop : operator * exp list -> exp_desc
  | Etuple : exp list -> exp_desc
  | Eapp : is_inline * exp *  exp list -> exp_desc
  | Esizeapp : exp * size list -> exp_desc
  | Elet : leq * exp -> exp_desc
  | Elocal : exp vardec list * eq * exp -> exp_desc
  | Erecord_access : exp * longname -> exp_desc
  | Erecord : (longname * exp) list -> exp_desc
  | Erecord_with : exp * (longname * exp) list -> exp_desc
  | Etypeconstraint : exp * type_expression -> exp_desc
  | Efun : funexp -> exp_desc
  | Ematch : exp * (exp, exp) match_handler list -> exp_desc
  | Epresent : (scondpat, exp) present_handler list * exp default -> exp_desc
  | Ereset : exp * exp -> exp_desc
  | Eassert : exp -> exp_desc
  | Eforloop : for_exp forloop -> exp_desc

and is_copy = bool

and is_rec = bool

and scondpat = scondpat_desc localized

and scondpat_desc =
  | Econdand : scondpat * scondpat -> scondpat_desc
  | Econdor : scondpat * scondpat -> scondpat_desc
  | Econdexp : exp -> scondpat_desc
  | Econdpat : exp * pattern -> scondpat_desc
  | Econdon : scondpat * exp -> scondpat_desc

and eq = eq_desc localized

and eq_desc =
  | EQeq : pattern * exp -> eq_desc
  (* [p = e] *)
  | EQsizefun : name * name list * exp -> eq_desc
  (* a size-parameterized expression [id <n1,...,nk> = e] *)
  | EQder :
      name * exp * exp option * (scondpat, exp) present_handler list -> eq_desc
  (* [der n = e [init e0] [reset p1 -> e1 | ... | pn -> en]] *)
  | EQinit : name * exp -> eq_desc
  (* [init n = e0 *)
  | EQemit : name * exp option -> eq_desc
  (* [emit n [= e] *)
  | EQif : exp * eq * eq -> eq_desc
  (* [if e then [... and ...] else [... and ...]] *)
  | EQand : eq list -> eq_desc
  (* parallel composition [eq1 and eq2] *)
  | EQlocal : exp vardec list * eq -> eq_desc
  (* local variables in an equation [local ... do eq done] *)
  | EQlet : leq * eq -> eq_desc
  (* local definition in an equation [let [rec] eq in eq] *)
  | EQreset : eq * exp -> eq_desc
  (* reset of an equation [reset eq every e] *)
  | EQautomaton : (exp, eq) block automaton_handler list *
        exp state option -> eq_desc
  (* automaton ... *)
  | EQmatch : exp * (exp, eq) match_handler list -> eq_desc
  | EQpresent :
      (scondpat, eq) present_handler list * eq default -> eq_desc
  | EQempty : eq_desc
  | EQassert : exp -> eq_desc
  | EQforloop : for_eq forloop -> eq_desc
  (* [foreach(s) [id in e..e]* [id in e [by e],]* returns (vardec_list) do eq] *)
  (* forward [e]* [id in e..e]* [id in e [by e],]* returns (vardec_list) do
     [until/unless e] done] *)

and 'body forloop =
  { for_size : exp option;
    for_kind : for_kind;
    for_index : name option;
    for_input : for_input_desc localized list;
    for_body : 'body;
    for_resume : bool; (* resume or restart *)
  }

(* result expression of a loop *)
and for_exp =
  | Forexp : { exp : exp; default : exp option } -> for_exp
  (* [for[each|ward] ... do e done] *)
  | Forreturns :
      { r_returns : for_vardec_desc localized list;
        r_block : (exp, eq) block } -> for_exp
  (* [for[each|ward] ... returns (...) local ... do eq ... done] *)

and for_vardec_desc =
  { for_array : int; (* 0 means x; 1 means [|x|]; 2 means [|[| x|]|]; etc *)
    for_vardec : exp vardec; (* [x [init e] [default e]] *)
  }
and for_eq =
  { for_out : for_out_desc localized list;
    (* [xi init vi] *)
    (* [xi] is an output; the successive values are accumulated *)
    (* [xi out x] *)
    (* [xi] are local output; [x] is the output st [xi = x.(i)] *)
    for_block : (exp, eq) block; (* loop body *)
  }

and for_kind =
  | Kforeach : for_kind
  (* parallel loop *)
  | Kforward : for_exit option -> for_kind
  (* iteration during one instant. The argument is the stoping condition *)

and for_exit = 
  { for_exit : exp;
    for_exit_kind : for_exit_kind }

and for_exit_kind = 
  | Ewhile | Euntil | Eunless

(* input definition for a loop *)
and for_input_desc =
  (* xi in e1 [by e2], that is, xi = e1.(i * e2) *)
  | Einput : { id: name; e : exp; by : exp option } -> for_input_desc
  (* [i in e1 to e2] or [i in e1 downto e2]; [e1] and [e2] must be sizes *)
  | Eindex :
      { id: name; e_left: exp; e_right : exp; dir: bool } -> for_input_desc

(* input patterns for loops *)
(* E.g., [xi]++[yi]++[|_|] in e] *)
and for_in_pat = for_in_pat_desc localized

and for_in_pat_desc =
  | Eloop_name : name -> for_in_pat_desc (* [xi] *)
  | Eloop_op : array_operator * for_in_pat list -> for_in_pat_desc
  | Eloop_pat : pattern -> for_in_pat_desc

(* outputs for loops *)
(* E.g., [xi]++[yi]++[|y|] out x *)
(* E.g., xi init e *)

(* output of a for loop in equational form *)
and for_out_desc =
  { for_name : name; (* xi [init e] [default e] [out x] *)
    for_out_name : name option; (* [xi out x] *)
    for_init : exp option;
    for_default : exp option;
  }

and 'body escape_desc =
  { e_cond: scondpat;
    e_reset: bool;
    e_let: leq list;
    e_body: 'body;
    e_next_state: exp state;
  }

and 'body escape = 'body escape_desc localized

and 'body automaton_handler_desc  =
  { s_state: statepat;
    s_let: leq list;
    s_body: 'body;
    s_until: 'body escape list;
    s_unless: 'body escape list;
  }

and 'body automaton_handler = 'body automaton_handler_desc localized

and 'a default =
  | Init : 'a -> 'a default | Else : 'a -> 'a default | NoDefault

and leq = leq_desc localized
and leq_desc = { l_kind: vkind; l_rec: is_rec; l_eq: eq }

and is_atomic = bool

and funexp_desc =
  { f_vkind: vkind; (* the kind for the arguments *)
    f_kind: kind; (* the kind for the body *)
    f_atomic: is_atomic;
    f_args: arg list;
    f_body: result
  }

and funexp = funexp_desc localized

and arg = exp vardec list

(* and arg1 =
  | Apat: pattern -> arg1
  | Avardec : exp vardec -> arg1 *)

and result = result_desc localized

and result_desc =
  | Exp: exp -> result_desc
  | Returns: exp vardec list * eq -> result_desc

(** Declarations *)
type interface = interface_desc localized

and interface_desc =
  | Einter_open : name -> interface_desc
  | Einter_typedecl :
      { name: name; ty_params: name list; ty_decl: type_decl } -> interface_desc
  | Einter_constdecl :
      { name: name; const: bool; ty: type_expression; info: name list }
      -> interface_desc

and type_decl = type_decl_desc localized

and type_decl_desc =
  | Eabstract_type : type_decl_desc
  | Eabbrev : type_expression -> type_decl_desc
  | Evariant_type : constr_decl list -> type_decl_desc
  | Erecord_type : (name * type_expression) list -> type_decl_desc

and constr_decl = constr_decl_desc localized

and constr_decl_desc =
  | Econstr0decl : name -> constr_decl_desc
  | Econstr1decl : name * type_expression list -> constr_decl_desc

type implementation = implementation_desc localized

and implementation_desc =
  | Eopen : name -> implementation_desc
  | Eletdecl : leq -> implementation_desc
  | Etypedecl :
      { name: name; ty_params: name list; ty_decl: type_decl } ->
      implementation_desc

type program = implementation list
