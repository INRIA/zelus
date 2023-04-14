(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2023 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

type 'a localized = { desc: 'a; loc: Location.t }

type name = String.t

(** Types *)
type type_expression = type_expression_desc localized

and type_expression_desc =
  | Etypevar : name -> type_expression_desc
  | Etypeconstr : Lident.t * type_expression list -> type_expression_desc
  | Etypetuple : type_expression list -> type_expression_desc
  | Etypefun : kind * type_expression * type_expression -> type_expression_desc

and kind =
  | Kfun : kind (* combinatorial *)
  | Knode : kind (* stateful node *)
  | Khybrid : kind (* stateful hybrid node *)
  | Kstatic : kind (* constant; known at instanciation time *)

(* constants *)
type immediate =
| Eint : int -> immediate
| Ebool : bool -> immediate
| Efloat : float -> immediate
| Evoid : immediate
| Echar : char -> immediate
| Estring : string -> immediate

(* synchronous operators *)
type operator =
  | Efby : operator
  (* unit delay *)
  | Eunarypre : operator
  (* unit delay *)
  | Eifthenelse : operator
  (* mux *)
  | Eminusgreater : operator
  (* initialization *)
  | Eseq : operator
  (* sequence *)
  | Erun : is_inline -> operator
  (* application of a statefull function *)
  | Eatomic : operator
  (* the argument is atomic *)
  | Etest : operator
  (* testing the presence of a signal *)
  | Eup : operator
  (* zero-crossing detection *)
  | Eperiod : operator
  (* period *)
  | Ehorizon : operator
  (* generate an event at a given horizon *)
  | Edisc : operator
  (* generate an event whenever x <> last x outside of integration *)
  | Earray_list : operator
  (* [| e1;...;en |] *)
  | Econcat : operator
  (* [ e1 ++ e2] *)
  | Eget : operator
  (* [e.(e)] *)
  | Eget_with_default : operator
  (* [e.(e) default e] *)
  | Eslice : operator
  (* [e.(e..e)] *)
  | Eupdate : operator
  (* [| e with e <- e |] *)
  
and is_inline = bool

type pateq = pateq_desc localized

and pateq_desc = Ident.t list

type 'exp vardec =
  { var_name: Ident.t; (* its name *)
    var_default: 'exp option; (* possible default value *)
    var_init: 'exp option; (* possible initial value for [last x] *)
    var_clock: bool; (* is-it a clock name ? *)
    var_loc: Location.t;
    var_typeconstraint: type_expression option;
    var_is_last: bool; (* is-there an access to [last x] ? *)
    mutable var_typ: Deftypes.typ; (* its type *)
  }

type 'a record = { mutable label: Lident.t; arg: 'a }

type pattern =
  { mutable pat_desc: pattern_desc;
    mutable pat_typ: Deftypes.typ;
    mutable pat_caus: Defcaus.tc; (* its causality type *)
    mutable pat_init: Definit.ti; (* its initialization type *)
    pat_loc: Location.t;
  }

and pattern_desc = 
  | Etuplepat : pattern list -> pattern_desc 
  | Evarpat : Ident.t -> pattern_desc 
  | Ewildpat : pattern_desc 
  | Econstpat : immediate -> pattern_desc 
  | Econstr0pat : Lident.t -> pattern_desc 
  | Econstr1pat : Lident.t * pattern list -> pattern_desc 
  | Ealiaspat : pattern * Ident.t -> pattern_desc 
  | Eorpat : pattern * pattern -> pattern_desc 
  | Erecordpat : pattern record list -> pattern_desc 
  | Etypeconstraintpat : pattern * type_expression -> pattern_desc 

type ('exp, 'eq) block =
  { b_vars: 'exp vardec list;
    b_body: 'eq;
    b_loc: Location.t;
    mutable b_write: Deftypes.defnames;
    mutable b_env: 'exp Deftypes.tentry Ident.Env.t }

type statepatdesc =
  | Estate0pat : Ident.t -> statepatdesc 
  | Estate1pat : Ident.t * Ident.t list -> statepatdesc

type statepat = statepatdesc localized

type 'exp state_desc =
  | Estate0 : Ident.t -> 'exp state_desc
  | Estate1 : Ident.t * 'exp list -> 'exp state_desc
  | Estateif : 'exp * 'exp state * 'exp state -> 'exp state_desc

and 'exp state = 'exp state_desc localized

type ('exp, 'body) match_handler =
  { m_pat : pattern;
    m_body: 'body;
    m_loc: Location.t;
    m_reset: bool; (* the handler is reset on entry *)
    m_zero: bool; (* the handler is done at a zero-crossing instant *)
    mutable m_env: 'exp Deftypes.tentry Ident.Env.t;
  }

(* the body of a present handler *)
type ('scondpat, 'exp, 'body) present_handler =
  { p_cond: 'scondpat;
    p_body: 'body;
    p_loc: Location.t;
    mutable p_env: 'exp Deftypes.tentry Ident.Env.t;
  }

type ('scondpat, 'exp, 'leq, 'body) escape =
  { e_cond: 'scondpat; 
    e_reset: bool; 
    e_let: 'leq list;
    e_body: 'body;
    e_next_state: 'exp state;
    e_loc: Location.t;
    mutable e_env: 'exp Deftypes.tentry Ident.Env.t;      
  }
                           
type is_weak = bool

type exp =
  { e_desc: exp_desc; (* descriptor *)
    e_loc: Location.t; (* location *)
    mutable e_typ: Deftypes.typ; (* its type *)
    mutable e_caus: Defcaus.tc;  (* its causality type *)
    mutable e_init: Definit.ti;  (* its initialization type *)
    }

and exp_desc = 
  | Econst : immediate -> exp_desc 
  | Econstr0 : { mutable lname: Lident.t } -> exp_desc 
  | Econstr1 : { mutable lname: Lident.t; arg_list: exp list } -> exp_desc 
  | Elocal : Ident.t -> exp_desc 
  | Eglobal :
      { mutable lname : Lident.t;
        mutable typ_instance : Deftypes.typ_instance } -> exp_desc 
  | Elast : Ident.t -> exp_desc 
  | Eop : operator * exp list -> exp_desc 
  | Etuple : exp list -> exp_desc 
  | Eapp : exp * exp list -> exp_desc 
  | Elet : leq * exp -> exp_desc 
  | Erecord_access : exp record -> exp_desc
  | Erecord : exp record list -> exp_desc
  | Erecord_with : exp * exp record list -> exp_desc
  | Etypeconstraint : exp * type_expression -> exp_desc
  | Efun : funexp -> exp_desc
  | Ematch : { mutable is_total : bool; e : exp;
               handlers : (exp, exp) match_handler list } -> exp_desc
  | Epresent :
      { handlers : (scondpat, exp, exp) present_handler list;
        default_opt : exp default } -> exp_desc
  | Ereset : exp * exp -> exp_desc
  | Eassert : exp -> exp_desc
  | Eforloop : for_exp forloop -> exp_desc

and 'body forloop =
  { for_size : exp option;
    for_kind : for_kind;
    for_index : for_index_desc localized list;
    for_body : 'body;
    for_env : exp Deftypes.tentry Ident.Env.t; }

(* result expression of a loop *)
and for_exp =
  | Forexp : { exp : exp; default : exp option } -> for_exp
  (* [for[each|ward] ... do e done] *)
  | Forreturns :
      { returns : for_vardec_desc localized list;
        body : (exp, eq) block;
        env : exp Deftypes.tentry Ident.Env.t; } -> for_exp
  (* [for[each|ward] ... returns (...) local ... do eq initialize ... done] *) 
  
and for_vardec_desc =
  { for_array : int; (* 0 means x; 1 means [|x|]; 2 means [|[| x|]|]; etc *)
    for_vardec : exp vardec; (* [x [init e] [default e]] *)
  }

and is_rec = bool

and scondpat = scondpat_desc localized

and scondpat_desc =
  | Econdand : scondpat * scondpat -> scondpat_desc
  | Econdor : scondpat * scondpat -> scondpat_desc
  | Econdexp : exp -> scondpat_desc
  | Econdpat : exp * pattern -> scondpat_desc
  | Econdon : scondpat * exp -> scondpat_desc

and leq =
  { l_rec: is_rec;
    l_eq: eq;
    l_loc: Location.t;
    mutable l_env: exp Deftypes.tentry Ident.Env.t;
  }
  
and eq =
  { eq_desc: eq_desc; (* descriptor *)
    mutable eq_write: Deftypes.defnames; (* set of defined variables *)
    eq_loc: Location.t; (* its location *)
  }

and eq_desc = 
  | EQeq : pattern * exp -> eq_desc  (* [p = e] *)
  | EQder :
      Ident.t * exp * exp option * (scondpat, exp, exp) present_handler list
      -> eq_desc  (* [der x = e [init e0] [reset z1 -> e1 | ...]] *)
  | EQinit : Ident.t * exp -> eq_desc  (* [init x = e] *)
  | EQemit : Ident.t * exp option -> eq_desc  (* [emit x [= e]] *)
  | EQif : exp * eq * eq -> eq_desc (* [if e then eq1 else eq2] *)
  | EQand : eq list -> eq_desc (* [eq1 and...and eqn] *)
  | EQlocal : (exp, eq) block -> eq_desc (* local x [...] do eq done *)
  | EQlet : leq * eq -> eq_desc (* let eq in eq *)
  | EQreset : eq * exp -> eq_desc (* [reset eq every e] *)
  | EQautomaton :
      { is_weak : bool;
        handlers : (exp, eq) block automaton_handler list;
        state_opt : exp state option } -> eq_desc
  | EQpresent :
      { handlers : (scondpat, exp, eq) present_handler list;
        default_opt : eq default } -> eq_desc
  | EQmatch :
      { mutable is_total : bool; e : exp;
        handlers : (exp, eq) match_handler list } -> eq_desc
  | EQempty : eq_desc
  | EQassert : exp -> eq_desc
  | EQforloop : for_eq forloop -> eq_desc
  (* [foreach [id in e..e]* [id in e [by e],]* returns (vardec_list) do eq] *)
  (* forward [id in e..e]* [id in e [by e],]* 
     [while e] do e] returns (vardec_list) *)

and for_eq =
  { for_out : for_out_desc localized list;
    for_block : (exp, eq) block; (* loop body *)
    for_out_env : exp Deftypes.tentry Ident.Env.t; 
  }

and for_kind =
  | Kforeach : for_kind
  (* parallel loop *)
  | Kforward : for_exit option -> for_kind
  (* iteration during one instant. The argument is the stoping condition *)

and for_exit = exp

(* index definition for a loop *)
and for_index_desc =
  | Einput : { id: Ident.t; e : exp; by : exp option } -> for_index_desc
  (* xi in e1 [by e2], that is, xi = e1.(i * e2) *)
  | Eindex :
      { id: Ident.t; e_left : exp; e_right : exp; dir : bool } -> for_index_desc
  (* [i in e1 to e2] or [i in e1 downto e2]; [e1] and [e2] must be sizes *)

(* output of a for loop in equational form *)
and for_out_desc =
  { for_name : Ident.t; (* xi [init e] [default e] [out x] *)
    for_out_name : Ident.t option; (* [xi out x] *)
    for_init : exp option;
    for_default : exp option;
  }
 
and 'body automaton_handler =
  { s_state: statepat;
    s_let: leq list;
    s_body: 'body;
    s_trans: (scondpat, exp, leq, 'body) escape list;
    s_loc: Location.t;
    mutable s_env: exp Deftypes.tentry Ident.Env.t;
    mutable s_reset: bool; (* is the state always entered by reset? *)
  }

and 'a default =
  | Init : 'a -> 'a default | Else : 'a -> 'a default | NoDefault

and is_atomic = bool

and funexp =
  { f_kind: kind; (* its kind *)
    f_atomic: is_atomic; (* when true, outputs depend strictly on all inputs *)
    f_args: arg list; (* list of arguments *)
    f_body: result;
    mutable f_env: exp Deftypes.tentry Ident.Env.t;
    f_loc: Location.t
  }

and arg = exp vardec list

and result =
  { r_desc: result_desc;
    mutable r_typ: Deftypes.typ; (* its type *)
    mutable r_caus: Defcaus.tc;  (* its causality type *)
    mutable r_init: Definit.ti;  (* its initialization type *)
    r_loc: Location. t }

and result_desc =
  | Exp: exp -> result_desc
  | Returns: (exp, eq) block -> result_desc


(** Declarations *)
type interface = interface_desc localized

and interface_desc =
  | Einter_open : name -> interface_desc 
  | Einter_typedecl : name * name list * type_decl -> interface_desc 
  | Einter_constdecl : name * type_expression * name list -> interface_desc 

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
  | Eletdecl : name * exp -> implementation_desc
  | Etypedecl : name * name list * type_decl -> implementation_desc

type program = implementation list

