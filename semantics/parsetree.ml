(* The ast is essentially that of first-order Zelus *)

(* untyped and uncausal streams *)
type 'a localized = { desc: 'a; loc: Location.t }

type name = String.t

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

(* constants *)
type const =
| Eint : int -> const
| Ebool : bool -> const
| Efloat : float -> const
| Echar : char -> const
| Estring : string -> const
| Evoid : const

(* synchronous operators *)
type operator =
| Efby : operator
| Eifthenelse : operator
| Eminusgreater : operator
| Eunarypre : operator

type pateq = pateq_desc localized

and pateq_desc = name list

type 'a default = 
  | Ewith_init : 'a -> 'a default    (* [local x init e in ...] *)
  | Ewith_default : 'a -> 'a default (* [local x default e in ... ] *)
  | Ewith_nothing : 'a default       (* [local x in ... ] *)
  | Ewith_last : 'a default          (* [local last x in ... ] *)

type 'exp vardec_desc =
  { var_name: name;
    var_default: 'exp default;
  }

and 'exp vardec = 'exp vardec_desc localized
                
type pattern = pattern_desc localized

and pattern_desc =
  | Econstr0pat : longname -> pattern_desc

type statepatdesc =
  | Estate0pat : name -> statepatdesc 
  | Estate1pat : name * name list -> statepatdesc

type statepat = statepatdesc localized

type 'exp state_expdesc =
  | Estate0 : name -> 'exp state_expdesc
  | Estate1 : name * 'exp list -> 'exp state_expdesc

type 'exp state_exp = 'exp state_expdesc localized

type ('scondpat, 'exp, 'body) escape_desc =
  { e_cond: 'scondpat; 
    e_reset: bool; 
    e_vars: 'exp vardec list;
    e_body: 'body;
    e_next_state: 'exp state_exp;
  }

and ('scondpat, 'exp, 'body) escape = ('scondpat, 'exp, 'body) escape_desc localized
                                    
type ('exp, 'body) match_handler_desc =
  { m_pat : pattern;
    m_vars: 'exp vardec list;
    m_body: 'body;
  }

and ('exp, 'body) match_handler = ('exp, 'body) match_handler_desc localized

type ('exp, 'body) automaton_handler_desc  =
  { s_state: statepat;
    s_vars: 'exp vardec list;
    s_body: 'body;
    s_until: ('exp, 'exp, 'body) escape list;
    s_unless: ('exp, 'exp, 'body) escape list;
  }

and ('exp, 'body) automaton_handler = ('exp, 'body) automaton_handler_desc localized

type is_weak = bool

type exp = exp_desc localized

and exp_desc = 
  | Econst : const -> exp_desc 
  | Econstr0 : longname -> exp_desc 
  | Econstr1 : longname * exp list -> exp_desc 
  | Evar : longname -> exp_desc 
  | Elast : name -> exp_desc 
  | Eop : operator * exp list -> exp_desc 
  | Eget : int * exp -> exp_desc 
  | Etuple : exp list -> exp_desc 
  | Eapp : longname * exp list -> exp_desc 
  | Elet : is_rec * eq * exp -> exp_desc 
  
and is_rec = bool
           
and scondpat = scondpat_desc localized

and scondpat_desc = exp_desc
                  
and eq = eq_desc localized

and eq_desc = 
  | EQeq : pateq * exp -> eq_desc
  | EQif : exp * eq * eq -> eq_desc
  | EQand : eq list -> eq_desc
  | EQlocal : exp vardec list * eq -> eq_desc
  | EQreset : eq * exp -> eq_desc
  | EQautomaton : (exp, eq) automaton_handler list -> eq_desc
  | EQmatch : exp * (exp, eq) match_handler list -> eq_desc
  | EQempty : eq_desc
  | EQassert : exp -> eq_desc

and kind =
  | Efun : kind
  | Enode : kind

and is_atomic = bool

type funexp_desc =
  { f_kind: kind;
    f_atomic: is_atomic;
    f_args: exp vardec list;
    f_res: exp vardec list;
    f_body: eq
  }

and funexp = funexp_desc localized
           
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
