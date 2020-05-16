(* The ast is essentially that of first-order Zelus *)

(* set of names *)
module S = Set.Make(Ident)

(* untyped and uncausal streams *)
type 'a localized = { desc: 'a; loc: Location.t }

(* constants *)
type const =
| Eint : int -> const
| Ebool : bool -> const
| Efloat : float -> const
| Evoid : const
| Estring : string -> const
| Echar : char -> const

(* synchronous operators *)
type operator =
| Efby : operator
| Eifthenelse : operator
| Eminusgreater : operator
| Eunarypre : operator

type pateq = pateq_desc localized

and pateq_desc = Ident.t list

type 'a default = 
  | Ewith_init : 'a -> 'a default    (* [local x init e in ...] *)
  | Ewith_default : 'a -> 'a default (* [local x default e in ... ] *)
  | Ewith_nothing : 'a default       (* [local x in ... ] *)
  | Ewith_last : 'a default          (* [local last x in ... ] *)

type 'exp vardec =
  { var_name: Ident.t;
    var_default: 'exp default;
    var_loc: Location.t;
  }

type pattern = pattern_desc localized

and pattern_desc = 
  | Econstr0pat : Lident.t -> pattern_desc
  
type statepatdesc =
  | Estate0pat : Ident.t -> statepatdesc 
  | Estate1pat : Ident.t * Ident.t list -> statepatdesc

type statepat = statepatdesc localized

type 'exp state_expdesc =
  | Estate0 : Ident.t -> 'exp state_expdesc
  | Estate1 : Ident.t * 'exp list -> 'exp state_expdesc

type 'exp state_exp = 'exp state_expdesc localized

type ('scondpat, 'exp, 'body) escape =
  { e_cond: 'scondpat; 
    e_reset: bool; 
    e_vars: 'exp vardec list;
    e_body: 'body;
    e_next_state: 'exp state_exp;
    e_loc: Location.t;
  }
                           
type ('exp, 'body) match_handler =
  { m_pat : pattern;
    m_vars: 'exp vardec list;
    m_body: 'body;
    m_loc: Location.t;
  }

type ('exp, 'body) automaton_handler =
  { s_state: statepat;
    s_vars: 'exp vardec list;
    s_body: 'body;
    s_trans: ('exp, 'exp, 'body) escape list;
    s_loc: Location.t;
  }

type is_weak = bool

type exp = { e_desc: exp_desc; e_loc: Location.t }

and exp_desc = 
  | Econst : const -> exp_desc 
  | Econstr0 : Lident.t -> exp_desc 
  | Econstr1 : Lident.t * exp list -> exp_desc 
  | Elocal : Ident.t -> exp_desc 
  | Eglobal : Lident.t -> exp_desc 
  | Elast : Ident.t -> exp_desc 
  | Eop : operator * exp list -> exp_desc 
  | Eget : int * exp -> exp_desc 
  | Etuple : exp list -> exp_desc 
  | Eapp : Lident.t * exp list -> exp_desc 
  | Elet : is_rec * eq * exp -> exp_desc 
  
and is_rec = bool
           
and eq =
  { eq_desc: eq_desc; (* descriptor *)
    eq_write: S.t; (* set of defined variables *)
    eq_loc: Location.t; (* its location *)
  }

and eq_desc = 
  | EQeq : pateq * exp -> eq_desc  (* [p = e] *)
  | EQif : exp * eq * eq -> eq_desc (* [if e then eq1 else eq2] *)
  | EQand : eq list -> eq_desc (* [eq1 and...and eqn] *)
  | EQlocal : exp vardec list * eq -> eq_desc (* local x [...] do eq done *)
  | EQreset : eq * exp -> eq_desc (* [reset eq every e] *)
  | EQautomaton : is_weak * (exp, eq) automaton_handler list -> eq_desc
  | EQmatch : exp * (exp, eq) match_handler list -> eq_desc
  | EQempty : eq_desc
  | EQassert : exp -> eq_desc
  
and kind =
  | Efun : kind
  | Enode : kind

and is_atomic = bool

type funexp =
  { f_kind: kind;
    f_atomic: is_atomic;
    f_args: exp vardec list;
    f_res: exp vardec list;
    f_body: eq;
    f_loc: Location.t
  }

type name = String.t

(** Declarations *)
type implementation = implementation_desc localized

and implementation_desc =
  | Eletdecl : name * exp -> implementation_desc
  | Eletfundecl : name * funexp -> implementation_desc
  | Etypedecl : name * type_decl -> implementation_desc
  
and type_decl = type_decl_desc localized
              
and type_decl_desc =
  | Evariant_type : constr_decl list -> type_decl_desc
                   
and constr_decl = constr_decl_desc localized
    
and constr_decl_desc =
  | Econstr0decl : name -> constr_decl_desc

type program = implementation list

