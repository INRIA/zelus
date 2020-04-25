(* The ast is essentially that of first-order Zelus *)

(* untyped and uncausal streams *)
type 'a localized = { desc: 'a; loc: Location.t }

(* constants *)
type const =
| Eint : int -> const
| Ebool : bool -> const
| Efloat : float -> const
| Evoid : const

(* synchronous operators *)
type operator =
| Efby : operator
| Eifthenelse : operator
| Eminusgreater : operator
| Eunarypre : operator

type pateq = String.t list

type 'a default = 
  | Ewith_init : 'a -> 'a default    (* [local x init e in ...] *)
  | Ewith_default : 'a -> 'a default (* [local x default e in ... ] *)
  | Ewith_nothing : 'a default       (* [local x in ... ] *)

type 'exp vardec =
  { var_name: String.t;
    var_default: 'exp default;
    var_loc: Location.t;
  }

type pattern = pattern_desc localized

and pattern_desc =
  | Econstr0pat : Lident.t -> pattern_desc
  | Econstr1pat : Lident.t * pattern list -> pattern_desc
  | Evarpat : String.t -> pattern_desc

type statepatdesc =
  | Estate0pat : String.t -> statepatdesc 
  | Estate1pat : String.t * String.t list -> statepatdesc

type statepat = statepatdesc localized

type 'exp state_expdesc =
  | Estate0 : String.t -> 'exp state_expdesc
  | Estate1 : String.t * 'exp list -> 'exp state_expdesc

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
    m_loc: Location.t }

type ('exp, 'body) automaton_handler =
  { s_state: statepat;
    s_vars: 'exp vardec list;
    s_body: 'body;
    s_trans: ('exp, 'exp, 'body) escape list;
    s_loc: Location.t;
  }

type is_weak = bool

type longname =
  | Name : String.t -> longname
  | Modname : { qual: String.t; id: String.t } -> longname
        
type exp = exp_desc localized

and exp_desc = 
  | Econst : const -> exp_desc 
  | Econstr0 : Lident.t -> exp_desc 
  | Econstr1 : Lident.t * exp list -> exp_desc 
  | Evar : longname -> exp_desc 
  | Elast : String.t -> exp_desc 
  | Eop : operator * exp list -> exp_desc 
  | Eget : int * exp -> exp_desc 
  | Etuple : exp list -> exp_desc 
  | Eapp : longname * exp list -> exp_desc 
  | Elet : is_rec * eq * exp -> exp_desc 
  
and is_rec = bool
           
and eq = { eq_desc: eq_desc; (* descriptor *)
           eq_loc: Location.t; (* its location in the source file *)
         }

and eq_desc = 
  | EQeq : pateq * exp -> eq_desc
  | EQinit : String.t * exp -> eq_desc
  | EQif : exp * eq * eq -> eq_desc
  | EQand : eq list -> eq_desc
  | EQlocal : exp vardec list * eq -> eq_desc
  | EQreset : eq * exp -> eq_desc
  | EQautomaton : is_weak * (exp, eq) automaton_handler list -> eq_desc
  | EQmatch : exp * (exp, eq) match_handler list -> eq_desc


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
    f_loc: Location.t;
  }

type implementation = implementation_desc localized

and implementation_desc =
  | Eletdef : string * exp -> implementation_desc
  | Eletfun : string * funexp -> implementation_desc

type program = implementation list
