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
  | Etypefun : kind * type_expression * type_expression -> type_expression_desc

and kind =
  | Kfun : kind
  | Knode : kind
  | Kstatic : kind

(* constants *)
type immediate =
| Eint : int -> immediate
| Ebool : bool -> immediate
| Efloat : float -> immediate
| Echar : char -> immediate
| Estring : string -> immediate
| Evoid : immediate

(* synchronous operators *)
type operator =
  | Efby : operator
  | Eifthenelse : operator
  | Eminusgreater : operator
  | Eunarypre : operator
  | Eseq : operator
  | Erun : is_inline -> operator
  | Eatomic : operator
  | Etest : operator
  | Eup : operator
  | Eperiod : operator
  
and is_inline = bool
              
type pateq = pateq_desc localized

and pateq_desc = name list

 
type 'exp vardec_desc =
  { var_name: name;
    var_default: 'exp option;
    var_init: 'exp option;
    var_clock: bool;
    var_typeconstraint: type_expression option;
  }

and 'exp vardec = 'exp vardec_desc localized
                
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

type ('scondpat, 'exp, 'body) escape_desc =
  { e_cond: 'scondpat; 
    e_reset: bool; 
    e_vars: 'exp vardec list;
    e_body: 'body;
    e_next_state: 'exp state;
  }

and ('scondpat, 'exp, 'body) escape =
  ('scondpat, 'exp, 'body) escape_desc localized
                                    
type ('scondpat, 'exp, 'body) automaton_handler_desc  =
  { s_state: statepat;
    s_vars: 'exp vardec list;
    s_body: 'body;
    s_until: ('scondpat, 'exp, 'body) escape list;
    s_unless: ('scondpat, 'exp, 'body) escape list;
  }

and ('scondpat, 'exp, 'body) automaton_handler =
  ('scondpat, 'exp, 'body) automaton_handler_desc localized

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
  | Elast : name -> exp_desc 
  | Eop : operator * exp list -> exp_desc 
  | Etuple : exp list -> exp_desc 
  | Eapp : exp *  exp list -> exp_desc 
  | Elet : is_rec * eq * exp -> exp_desc 
  | Erecord_access : exp * longname -> exp_desc
  | Erecord : (longname * exp) list -> exp_desc
  | Erecord_with : exp * (longname * exp) list -> exp_desc
  | Etypeconstraint : exp * type_expression -> exp_desc
  | Efun : funexp -> exp_desc
  | Ematch : exp * (exp, exp) match_handler list -> exp_desc
  | Epresent : (scondpat, exp) present_handler list * exp default -> exp_desc
  | Ereset : exp * exp -> exp_desc
  
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
  | EQder : name * exp -> eq_desc
  | EQinit : name * exp -> eq_desc
  | EQemit : name * exp option -> eq_desc
  | EQif : exp * eq * eq -> eq_desc
  | EQand : eq list -> eq_desc
  | EQlocal : exp vardec list * eq -> eq_desc
  | EQreset : eq * exp -> eq_desc
  | EQautomaton :
      (scondpat, exp, eq) automaton_handler list * exp state option -> eq_desc
  | EQmatch : exp * (exp, eq) match_handler list -> eq_desc
  | EQpresent :
      (scondpat, eq) present_handler list * eq default -> eq_desc
  | EQempty : eq_desc
  | EQassert : exp -> eq_desc

and 'a default =
  | Init : 'a -> 'a default | Else : 'a -> 'a default | NoDefault

and is_atomic = bool

and funexp_desc =
  { f_kind: kind; 
    f_atomic: is_atomic; 
    f_args: arg list;
    f_body: result
  }

and funexp = funexp_desc localized

and arg = exp vardec list
        
and result = result_desc localized

and result_desc =
  | Exp: exp -> result_desc
  | Returns: exp vardec list * eq -> result_desc

(** Declarations *)
type interface = interface_desc localized

and interface_desc =
  | Einter_open : name -> interface_desc 
  | Einter_typedecl : name * name list * type_decl -> interface_desc 
  | Einter_constdecl :
      name * type_expression * name list -> interface_desc 

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
