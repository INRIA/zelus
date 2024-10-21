(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

%{

open Lexing
open Location
open Parsetree

let localise start_pos end_pos = Loc(start_pos.pos_cnum, end_pos.pos_cnum)

let make desc start_pos end_pos =
  { desc = desc; loc = localise start_pos end_pos }

let make_name op start_pos end_pos =
  make (Evar(Name(op))) start_pos end_pos

let unop op e start_pos end_pos =
  Eapp(false, make_name op start_pos end_pos, [e])
let binop op e1 e2 start_pos end_pos =
  Eapp(false, make_name op start_pos end_pos, [e1; e2])

let unary_minus op e start_pos end_pos =
  match op, e.desc with
    | "-", Econst(Eint v) -> Econst(Eint(-v))
    | ("-" | "_."), Econst(Efloat v) -> Econst(Efloat(-.v))
    | _ -> unop ("~" ^ op) e start_pos end_pos

let unary_minus_int x = -x
and unary_minus_float x = -.x

(* Representation of lists. [] for Stdlib.[] *)
(* [e1;...;en] for Stdlib.(::) e1 (... Stdlib.[]) *)
let nil_name = "[]"
let cons_name = "::"

let list_name n = Name(n)

let nil_desc = Evar(list_name nil_name)

let cons_desc x l start_pos end_pos =
  Eapp(false,
       make (Evar(list_name cons_name)) start_pos end_pos,
       [make (Etuple [x; l]) start_pos end_pos])

let rec cons_list_desc l start_pos end_pos =
  match l with
  | [] -> nil_desc
  | x :: l -> cons_desc x (cons_list l start_pos end_pos) start_pos end_pos

and cons_list l start_pos end_pos =
  make (cons_list_desc l start_pos end_pos) start_pos end_pos

let no_eq start_pos end_pos = make (EQempty) start_pos end_pos

(* constructors with arguments *)
let app i f l =
  match f.desc, l with
  | Econstr0(id), [{ desc = Etuple(arg_list) }] ->
     (* C(e1,...,en) *)
     Econstr1(id, arg_list)
  | Econstr0(id), [arg] ->
     Econstr1(id, [arg])
  | _ -> Eapp(i, f, l)

let constr f e =
  match e.desc with
  | Etuple(arg_list) ->
    (* C(e1,...,en) *) Econstr1(f, arg_list)
  | _ ->
     (* C(e) *) Econstr1(f, [e])

let constr_pat f p =
  match p.desc with
  | Etuplepat(arg_list) ->
    (* C(p1,...,pn) *) Econstr1pat(f, arg_list)
  | _ ->
     (* C(p) *) Econstr1pat(f, [p])

let scond_true start_pos end_pos =
  make (Econdexp(make (Econst(Ebool(true))) start_pos end_pos))
       start_pos end_pos

(* building a function *)
(* [let node (const x1 ... xn) (static y1 ... ym) m1 mk = e in ... ] *)
(* is represented as *)
(* [let f = fun (const x1...xn) -> fun (static y1...ym) -> fun m1...mk -> e in ...]*)
let fun_one_desc is_atomic kind vkind p_list result startpos endpos =
  Efun(make { f_atomic = is_atomic; f_vkind = vkind;
              f_kind = kind; f_args = p_list;
	      f_body = result }
	    startpos endpos)

let rec funexp_desc is_atomic kind v_p_list_list result startpos endpos =
  match v_p_list_list with
  | [] -> assert false
  | [vkind, p_list] ->
       fun_one_desc is_atomic kind vkind p_list result startpos endpos
  | (vkind, p_list) :: v_p_list_list ->
       fun_one_desc is_atomic (Kfun(Kany)) vkind p_list
               (make (Exp (funexp is_atomic kind v_p_list_list result startpos endpos))
		     startpos endpos)
               startpos endpos
and funexp is_atomic kind v_p_list_list result startpos endpos =
  make (funexp_desc is_atomic kind v_p_list_list result startpos endpos)
       startpos endpos

(* building a for loop *)
let forward_loop resume (size_opt, index_opt, input_list, opt_cond, body) =
  { for_size = size_opt;
    for_kind = Kforward(opt_cond);
    for_index = index_opt;
    for_input = input_list;
    for_body = body;
    for_resume = resume }

let foreach_loop resume (size_opt, index_opt, input_list, body) =
  { for_size = size_opt;
    for_kind = Kforeach;
    for_index = index_opt;
    for_input = input_list;
    for_body = body;
    for_resume = resume }

%}

%token <string> CONSTRUCTOR
%token <string> IDENT
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <string> STRING
%token <char> CHAR

%token AMPERAMPER     /* "&&" */
%token AMPERSAND      /* "&" */
%token AND            /* "and" */
%token AS             /* "as" */
%token ASSERT         /* "assert" */
%token ATOMIC         /* "atomic" */
%token AUTOMATON      /* "automaton" */
%token BAR            /* "|" */
%token BARBAR         /* "||" */
%token BY             /* "by" */
%token CLOCK          /* "clock" */
%token COLON          /* ":" */
%token COMMA          /* "," */
%token CONST          /* "const" */
%token CONTINUE       /* "continue" */
%token DEFAULT        /* "default" */
%token DO             /* "do" */
%token DONE           /* "done" */
%token DOT            /* "." */
%token DOTDOT         /* ".." */
%token DOWNTO         /* "downto" */
%token DER            /* "der" */
%token DIV            /* "/" */
%token ELSE           /* "else" */
%token EMIT           /* "emit" */
%token END            /* "end" */
%token EQUAL          /* "=" */
%token EQUALEQUAL     /* "==" */
%token EVERY          /* "every" */
%token EXCEPTION      /* "exception" */
%token EXTERNAL       /* "external" */
%token FBY            /* "fby" */
%token FUN            /* "fun" */
%token GREATER        /* ">" */
%token GGREATER       /* ">>" */
%token HYBRID         /* "hybrid" */
%token HORIZON        /* "horizon" */
%token FOREACH        /* "foreach" */
%token FORWARD        /* "forward" */
%token IF             /* "if" */
%token IN             /* "in" */
%token INIT           /* "init" */
%token INLINE         /* "inline" */
%token LAST           /* "last" */
%token LAST_STAR      /* "last*" */
%token LBRACE         /* "{" */
%token LESSER         /* "<" */
%token LLESSER        /* "<<" */
%token RBRACE         /* "}" */
%token LBRACKET       /* "[" */
%token RBRACKET       /* "]" */
%token LBRACKETBAR    /* "[|" */
%token RBRACKETBAR    /* "|]" */
%token LET            /* "let" */
%token LESSMINUS      /* "<-" */
%token LOCAL          /* "local" */
%token LPAREN         /* "(" */
%token RPAREN         /* ")" */
%token MATCH          /* "match" */
%token MINUS          /* "-" */
%token MINUSGREATER   /* "->" */
%token AFUN           /* "-A->" */
%token DFUN           /* "-D->" */
%token SFUN           /* "-S->" */
%token VFUN           /* "-V->" */
%token CFUN           /* "-C->" */
%token NODE           /* "node" */
%token OF             /* "of" */
%token ON             /* "on" */
%token OPEN           /* "open" */
%token OR             /* "or" */
%token OUT            /* "out" */
%token PERIOD         /* "period" */
%token PLUS           /* "+" */
%token PLUSPLUS       /* "++" */
%token PRE            /* "pre" */
%token PRESENT        /* "present" */
%token QUOTE          /* "'" */
%token REC            /* "rec" */
%token RESET          /* "reset" */
%token RESUME         /* "resume" */
%token RETURNS        /* "returns" */
%token RUN            /* "run" */
%token SEMI           /* ";" */
%token STAR           /* "*" */
%token STATIC         /* "static" */
%token TEST           /* "?" */
%token THEN           /* "then" */
%token TO             /* "to" */
%token TYPE           /* "type" */
%token TRANSPOSE      /* "transpose" */
%token FLATTEN        /* "flatten" */
%token REVERSE        /* "reverse" */
%token UNDERSCORE     /* "_" */
%token UNLESS         /* "unless" */
%token UNTIL          /* "until" */
%token UP             /* "up" */
%token VAL            /* "val" */
%token WHERE          /* "where" */
%token WHILE          /* "while" */
%token WITH           /* "with" */

%token <string> PREFIX
%token <string> INFIX0
%token <string> INFIX1
%token <string> INFIX2
%token <string> SUBTRACTIVE
%token <string> INFIX3
%token <string> INFIX4
%token EOF

%nonassoc prec_result
%left WHERE AND
%nonassoc EMIT
%nonassoc ASSERT
%nonassoc prec_seq
%right SEMI
%nonassoc prec_der_with_reset
%nonassoc prec_present
%nonassoc prec_ident
%right prec_list
%left EVERY
%nonassoc PRESENT
%nonassoc THEN
%nonassoc ELSE
%nonassoc WITH
%left  AS
%left  BAR
%nonassoc END
%left COMMA
%left TO DOWNTO
%left prec_in_input
%left RPAREN
%nonassoc prec_minus_greater
%nonassoc FBY
%right MINUSGREATER VFUN SFUN DFUN CFUN AFUN 
%left OR BARBAR
%left AMPERSAND AMPERAMPER
%left INFIX0 LESSER GREATER EQUAL
%nonassoc RESET
%right INFIX1
%left INFIX2 PLUS SUBTRACTIVE MINUS PLUSPLUS
%left DIV
%left STAR INFIX3
%left INFIX4
%left ON
%right prec_uminus
%right PREFIX
%right PRE TEST UP
%left TRANSPOSE FLATTEN REVERSE
%left DOT
%left INIT DEFAULT

%start implementation_file
%type <Parsetree.implementation list> implementation_file

%start interface_file
%type <Parsetree.interface list> interface_file

%start scalar_interface_file
%type <Parsetree.interface list> scalar_interface_file

%%

/** Tools **/

/* Separated list */
list_aux(S, X):
| x = X { [x] }
| r = list_aux(S, X) S x = X { x :: r }
;

%inline list_of(S, X):
   r = list_aux(S, X) { List.rev r }
;

%inline empty(X):
  | { [] }
  | r = X { r }
;

/* Non separated list */
list_aux_no_sep(X):
| x = X { [x] }
| r = list_aux_no_sep(X) x = X { x :: r }
;

%inline list_no_sep_of(X):
   r = list_aux_no_sep(X) { List.rev r }
;

/* Localization */
%inline localized(X):
| x = X { make x $startpos $endpos }
;

%inline optional(X):
  | /* empty */
      { None }
  | x = X
      { Some(x) }
;

/* Nested [|[|...X...|]|] */
array_of(X):
  | x = X { (0, x) }
  | LBRACKETBAR x = array_of(X) RBRACKETBAR
    { fst x + 1, snd x }
;

/* Interface */
interface_file:
  | EOF
      { [] }
  | il = decl_list(localized(interface)) EOF
      { List.rev il }
;

interface:
  | OPEN c = CONSTRUCTOR
      { Einter_open(c) }
  | TYPE tp = type_params i = IDENT
    td = localized(type_declaration_desc)
    { Einter_typedecl
	{ name = i; ty_params = tp; ty_decl = td } }
  | v = val_or_const i = ide COLON t = type_expression
      { Einter_constdecl { name = i; const = v; ty = t; info = [] } }
;

/* Scalar interface */
scalar_interface_file:
  | EOF
      { [] }
  | il = decl_list(scalar_interface) EOF
      { List.rev (List.flatten il) }
  ;

scalar_interface :
  | OPEN c = CONSTRUCTOR
      { [make (Einter_open(c)) $startpos $endpos] }
  | TYPE tp = type_params i = IDENT td = localized(type_declaration_desc)
    { [make (Einter_typedecl { name = i; ty_params = tp;
			       ty_decl = td }) $startpos $endpos] }
  | v = val_or_const i = ide COLON t = type_expression
    { [make (Einter_constdecl { name = i; const = v; ty = t; info = [] })
       $startpos $endpos] }
  | EXTERNAL i = ide COLON t = type_expression EQUAL l = list_no_sep_of(STRING)
    { [make (Einter_constdecl { name = i; const = false;
				ty = t; info = l }) $startpos $endpos] }
  | EXCEPTION constructor
      { [] }
  | EXCEPTION constructor OF type_expression
      { [] }
;

type_declaration_desc:
  | /* empty */
      { Eabstract_type }
  | EQUAL l = list_of(BAR, localized(constr_decl_desc))
      { Evariant_type (l) }
  | EQUAL BAR l = list_of(BAR, localized(constr_decl_desc))
      { Evariant_type (l) }
  | EQUAL LBRACE s = label_list(label_type) RBRACE
      { Erecord_type (s) }
  | EQUAL t = type_expression
      { Eabbrev(t) }
;

val_or_const :
  | VAL { false }
  | CONST { true }
;

type_params :
  | LPAREN tvl = list_of(COMMA, type_var) RPAREN
      { tvl }
  | tv = type_var
      { [tv] }
  |
      { [] }
;

label_list(X):
  | x = X
      { [x] }
  | x = X SEMI
      { [x] }
  | x = X SEMI ll = label_list(X)
      { x :: ll }
;

label_type:
  i = IDENT COLON t = type_expression
  { (i, t) }
;

constr_decl_desc:
  | c = CONSTRUCTOR
      { Econstr0decl(c) }
  | c = CONSTRUCTOR OF l = list_of(STAR, simple_type)
      { Econstr1decl(c, l) }
;

implementation_file:
  | EOF
      { [] }
  | i = decl_list(localized(implementation)) EOF
      { List.rev i }
;

decl_list(X):
  | dl = decl_list(X) x = X
      { x :: dl }
  | x = X
      { [x] }
;

implementation:
  | OPEN c = CONSTRUCTOR
    { Eopen c }
  | TYPE tp = type_params id = IDENT
    td = localized(type_declaration_desc)
    { Etypedecl
	{ name = id; ty_params = tp; ty_decl = td } }
  | LET v = vkind_opt i = is_rec let_eq = equation_and_list
    { Eletdecl(make 
                 { l_rec = i; l_kind = v; l_eq = let_eq } $startpos $endpos) }
;

vkind:
  | CONST { Kconst }
  | STATIC { Kstatic }
;

vkind_opt:
  | v = vkind { v }
  | { Kany }
;

fun_kind:
  | FUN    { Kfun(Kany) }
  | NODE   { Knode(Kdiscrete) }
  | HYBRID { Knode(Kcont) }
;

%inline fun_kind_opt:
  | { Kfun(Kany) }
  | f = fun_kind { f }
;

%inline is_atomic:
  | ATOMIC { true }
  | { false }
;


result:
  | RETURNS p = param eq = equation
    { make (Returns(p, eq)) $startpos $endpos }
  | EQUAL seq = seq_expression %prec prec_result
    { make (Exp(seq)) $startpos(seq) $endpos(seq) }
  | EQUAL seq = seq_expression WHERE 
      v = vkind_opt i = is_rec eq = where_equation_and_list %prec prec_result
    { make (Exp(make (Elet(make { l_rec = i; l_kind = v; l_eq = eq }
			  $startpos(eq) $endpos(eq), seq))
		$startpos(seq) $endpos(eq)))
      $startpos $endpos }
;

%inline where_equation_and_list:
  | l = where_equation_and_list_aux
    { match List.rev l with
      | [] -> no_eq $startpos $endpos | [eq] -> eq
      | l -> make (EQand(l)) $startpos $endpos }
;

where_equation_and_list_aux:
  | eq = equation
     { [eq] }
  | eq_list = where_equation_and_list_aux AND eq = equation
    { eq :: eq_list }
;

for_return:
  | fv = for_vardec
    { [fv] }
  | LPAREN l = optional(list_of(COMMA, for_vardec)) RPAREN
    { match l with None -> [] | Some(l) -> l }
;

for_vardec:
  | p = array_of(vardec)
    { make { for_array = fst p; for_vardec = snd p } $startpos $endpos }
;

equation_and_list:
  | l = list_of(AND, equation)
    { match l with
      | [] -> no_eq $startpos $endpos | [eq] -> eq
      | l -> make (EQand(l)) $startpos $endpos }
;

equation_empty_and_list:
  | l_opt = optional(list_of(AND, equation))
    { match l_opt with | None -> make EQempty $startpos $endpos
		       | Some([eq]) -> eq
		       | Some(l) -> make (EQand(l)) $startpos $endpos }
;

equation:
   eq = localized(equation_desc) { eq }
;

/* a single equation; either ended by a terminal or an expression */
equation_desc:
  | LOCAL v_list = vardec_comma_list IN eq = equation
    { EQlocal(v_list, eq) } 
  | LOCAL v_list = vardec_comma_list DO eq = equation_empty_and_list DONE
    { EQlocal(v_list, eq) } 
  | DO eq = equation_empty_and_list DONE
    { eq.desc }
  | RESET eq = equation_and_list EVERY e = expression
    { EQreset(eq, e) }
  | LET v = vkind_opt i = is_rec let_eq = equation_and_list IN eq = equation
    { EQlet(make { l_rec = i; l_kind = v; l_eq = let_eq}
	    $startpos $endpos(let_eq), eq) }
  | AUTOMATON opt_bar a = automaton_handlers(equation_empty_and_list) END
    { EQautomaton(List.rev a, None) }
  | AUTOMATON opt_bar
       a = automaton_handlers(equation_empty_and_list) INIT e = state END
    { EQautomaton(List.rev a, Some(e)) }
  | MATCH e = seq_expression WITH opt_bar
    m = match_handlers(equation) opt_end
    { EQmatch(e, List.rev m) }
  | IF e = seq_expression THEN eq1 = equation
    ELSE eq2 = equation opt_end
    { EQif(e, eq1, eq2) }
  | IF e = seq_expression THEN eq1 = equation opt_end
      { EQif(e, eq1, no_eq $startpos $endpos) }
  | IF e = seq_expression ELSE eq2 = equation opt_end
      { EQif(e, no_eq $startpos $endpos, eq2) }
  | PRESENT opt_bar p = present_handlers(equation) opt_end
    { EQpresent(List.rev p, NoDefault) }
  | PRESENT opt_bar p = present_handlers(equation)
    ELSE eq = equation opt_end
    { EQpresent(List.rev p, Else(eq)) }
  | ASSERT e = expression
    { EQassert(e) }
  | EMIT i = ide
      { EQemit(i, None) }
  | EMIT i = ide EQUAL e = seq_expression
      { EQemit(i, Some(e)) }
  | INIT i = ide EQUAL e = seq_expression
      { EQinit(i, e) }
  | p = pattern EQUAL e = seq_expression
      { EQeq(p, e) }
  | ide = ide LLESSER ide_list = list_of(COMMA, ide) GGREATER EQUAL 
        e = seq_expression
    { EQsizefun(ide, ide_list, e) }
  | a = is_atomic k = fun_kind_opt ide = ide 
       LLESSER ide_list = list_of(COMMA, ide) GGREATER 
       v_p_list_list = param_list_list r = result
    { EQsizefun(ide, ide_list, funexp a k v_p_list_list r 
                                   $startpos(v_p_list_list) $endpos) }
  | a = is_atomic k = fun_kind_opt ide = ide v_p_list_list = param_list_list 
    r = result
    { EQeq(make (Evarpat ide) $startpos(ide) $endpos(ide),
	   funexp a k v_p_list_list r $startpos $endpos) }
  | DER i = ide EQUAL e = seq_expression opt = optional(init_expression)
      { EQder(i, e, opt, []) }
  | DER i = ide EQUAL e = seq_expression opt = optional(init_expression)
    RESET p = present_handlers(expression) %prec prec_der_with_reset
    { EQder(i, e, opt, p) }
  | FOREACH f = foreach_loop_eq
    { EQforloop (foreach_loop false f) }
  | FORWARD f = forward_loop_eq
    { EQforloop (forward_loop false f) }
  | FORWARD RESUME f = forward_loop_eq
    { EQforloop (forward_loop true f) }
;

/* states of an automaton in an equation*/
automaton_handlers(X):
  | a = automaton_handler(X)
      { [a] }
  | ahs = automaton_handlers(X) BAR a = automaton_handler(X)
      { a :: ahs }
;

automaton_handler(X):
  | sp = state_pat MINUSGREATER l = let_list b = block(X) DONE
    { make { s_state = sp; s_let = l; s_body = b; s_until = []; s_unless = [] }
      $startpos $endpos } 
  | sp = state_pat MINUSGREATER l = let_list b = block(X) THEN e = emission(X)
    { let body_e, st_e = e in
      make { s_state = sp; s_let = l; s_body = b;
	     s_until =
               [make { e_cond = scond_true $endpos(b) $startpos(e);
                       e_reset = true; e_let = [];
		       e_body = body_e; e_next_state = st_e }
		$endpos(b) $endpos(e) ];
	     s_unless = [] } $startpos $endpos }
  | sp = state_pat MINUSGREATER l = let_list b = block(X)
    CONTINUE e = emission(X)
    { let body_e, st_e = e in
      make { s_state = sp; s_let = l; s_body = b;
	     s_until =
               [make { e_cond = scond_true $endpos(b) $startpos(e);
                       e_reset = false; e_let = []; e_body = body_e;
		       e_next_state = st_e } $endpos(b) $endpos(e)];
	   s_unless = [] } $startpos $endpos }
  | sp = state_pat MINUSGREATER l = let_list b = block(X)
    UNTIL el = list_of(UNTIL, escape(X))
    { make { s_state = sp; s_let = l; s_body = b;
	     s_until = el; s_unless = [] } $startpos $endpos }
  | sp = state_pat MINUSGREATER l = let_list b = block(X)
    UNLESS el = list_of(UNLESS, escape(X))
    { make { s_state = sp; s_let = l; s_body = b;
	     s_until = []; s_unless = el } $startpos $endpos }
;

escape(X) :
  | sc = scondpat THEN l = let_list e = emission(X)
    { let e_body, s = e in
      make { e_cond = sc; e_reset = true; e_let = l;
	     e_body = e_body; e_next_state = s }
      $startpos $endpos }
  | sc = scondpat CONTINUE l = let_list e = emission(X)
    { let e_body, s = e in
      make { e_cond = sc; e_reset = false; e_let = l;
	     e_body = e_body; e_next_state = s }
      $startpos $endpos }
;

state :
  | c = CONSTRUCTOR
      { make (Estate0(c)) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN e = expression RPAREN
      { make (Estate1(c, [e])) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN l = expression_comma_list RPAREN
    { make (Estate1(c, List.rev l)) $startpos $endpos }
  | IF e = expression THEN s1 = state ELSE s2 = state
    { make (Estateif(e, s1, s2)) $startpos $endpos }
;

state_pat :
  | c = CONSTRUCTOR
      { make (Estate0pat(c)) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN l = list_of(COMMA, IDENT) RPAREN
      { make (Estate1pat(c, l)) $startpos $endpos }
;

/* Pattern on a signal */
scondpat :
  | sc = localized(scondpat_desc) { sc }
;

scondpat_desc :
  | e = simple_expression p = simple_pattern
      { Econdpat(e, p) }
  | e = simple_expression
      { Econdexp(e) }
  | scpat1 = scondpat AMPERSAND scpat2 = scondpat
      { Econdand(scpat1, scpat2) }
  | scpat1 = scondpat BAR scpat2 = scondpat
      { Econdor(scpat1, scpat2) }
  | scpat1 = scondpat ON e = simple_expression
    { Econdon(scpat1, e) }
;

/* Block */
block(X):
  | lo = local_list DO x = X
      { make { b_vars = lo; b_body = x } $startpos $endpos }
;

emission(X):
  | s = state
    { make { b_vars = []; b_body = no_eq $startpos $endpos }
      $startpos $endpos, s }
  | b = block(X) IN s = state
    { b, s }
;

let_list:
  | /* empty */
      { [] }
  | o = one_let IN l = let_list
      { o :: l }
;

one_let:
  | LET v = vkind_opt i = is_rec eq = equation_and_list
    { make { l_rec = i; l_kind = v; l_eq = eq } $startpos $endpos }
;

local_list:
  | /* empty */
      { [] }
  | LOCAL v_list = vardec_comma_list
      { v_list }
;

vardec_comma_list:
  | l = list_of(COMMA, vardec)
    { l }
;

vardec_empty_comma_list:
  | l = optional(vardec_comma_list)
    { match l with None -> [] | Some(l) -> l }
;


param_list_list:
  | l = list_no_sep_of(param)
    { [Kany, l] }
  | l = list_no_sep_of(vkind_param_list)
    { l }
  | lp = list_no_sep_of(vkind_param_list) l = list_no_sep_of(param)
    { lp @ [Kany, l] }
;

/* %inline vkind_param_list_opt:
  | v = vkind_param_list
    { v }
  | l = list_no_sep_of(param)
    { Kany, l }
;
*/

vkind_param_list:
  | LPAREN v = vkind l = param_list RPAREN
    { v, l }
;

param_list:
  | l = list_no_sep_of(param)
    { l }
;

param:
  | LPAREN v = vardec_empty_comma_list RPAREN
    { v }
  | ide = ide
    { [ make { var_name = ide; var_clock = false;
	       var_init = None; var_default = None;
	       var_typeconstraint = None; var_is_last = false }
	$startpos $endpos ] }
;

vardec:
  | l = optional(LAST)
    c = optional(CLOCK) ide = ide t_opt = optional(colon_type_expression)
    i_opt = optional(init_expression)
    d_opt = optional(default_expression)
    { make { var_name = ide;
	     var_clock = (match c with | None -> false | Some _ -> true);
	     var_init = i_opt; var_default = d_opt;
	     var_typeconstraint = t_opt;
	     var_is_last = (match l with | None -> false | Some _ -> true) }
      $startpos $endpos }
;

colon_type_expression:
  | COLON t = type_expression
    { t }
;

init_expression:
  | INIT e = expression
    { e }
;

default_expression:
  | DEFAULT e = expression
    { e }
;

opt_bar:
  | BAR             { () }
  | /*epsilon*/     { () }
;

/* Testing the presence of a signals */
present_handlers(X):
  | p = present_handler(X)
      { [ p ] }
  | ps = present_handlers(X) BAR p = present_handler(X)
      { p :: ps }
;

present_handler(X):
  | sc = scondpat MINUSGREATER x = X
      { make { p_cond = sc; p_body = x } $startpos $endpos }
;
/* Pattern matching */
match_handlers(X):
  | m = match_handler(X)
      { [ m ] }
  | mh = match_handlers(X) BAR m = match_handler(X)
      { m :: mh }
;

match_handler(X):
  | p = pattern MINUSGREATER eq = X
      { make { m_pat = p; m_body = eq } $startpos $endpos }
;

/* Patterns */
pattern:
  | p = simple_pattern
      { p }
  | p = pattern AS i = IDENT
      { make (Ealiaspat(p, i)) $startpos $endpos }
  | p1 = pattern BAR p2 = pattern
      { make (Eorpat(p1, p2)) $startpos $endpos }
  | p = pattern_comma_list %prec prec_list
      { make (Etuplepat(List.rev p)) $startpos $endpos }
  | c = constructor p = simple_pattern
      { make (constr_pat c p) $startpos $endpos }
;

simple_pattern:
  | a = atomic_constant
      { make (Econstpat a) $startpos $endpos }
  | MINUS i = INT
      { make (Econstpat(Eint(unary_minus_int i))) $startpos $endpos }
  | MINUS f = FLOAT
      { make (Econstpat(Efloat(unary_minus_float f))) $startpos $endpos }
  | c = constructor
      { make (Econstr0pat(c)) $startpos $endpos }
  | i = ide
      { make (Evarpat i) $startpos $endpos }
  | LPAREN p = pattern RPAREN
      { p }
  | LPAREN p = pattern_comma_list RPAREN
      { make (Etuplepat (List.rev p)) $startpos $endpos }
  | LPAREN RPAREN
      { make (Econstpat(Evoid)) $startpos $endpos }
  | UNDERSCORE
      { make Ewildpat $startpos $endpos }
  | LPAREN p = pattern COLON t = type_expression RPAREN
      { make (Etypeconstraintpat(p, t)) $startpos $endpos }
  | LBRACE p = pattern_label_list RBRACE
      { make (Erecordpat(p)) $startpos $endpos }
;

pattern_comma_list:
  | p1 = pattern COMMA p2 = pattern
      { [p2; p1] }
  | pc = pattern_comma_list COMMA p = pattern
      { p :: pc }
;

pattern_label_list :
  | p = pattern_label SEMI pl = pattern_label_list
      { p :: pl }
  | p = pattern_label
      { [p] }
  | UNDERSCORE
      { [] }
  | /*epsilon*/
      { [] }
;

pattern_label :
  | ei = ext_ident EQUAL p = pattern
      { (ei, p) }
;

/* Expressions */
seq_expression :
  | e = expression SEMI seq = seq_expression
      { make (Eop(Eseq, [e; seq])) $startpos $endpos }
  | e = expression %prec prec_seq
      { e }
;


/* Simple expressions - that is, well parenthesized expressions */
simple_expression_list:
  | l = list_no_sep_of(simple_expression)
    { l }
;

simple_expression:
  | l = localized(simple_expression_desc)
    { l } 
;

simple_expression_desc:
  | c = constructor
      { Econstr0(c) }
  | i = ext_ident
      { Evar i }
  | e = simple_expression LLESSER s_e_list = size_expression_list GGREATER 
    { Esizeapp(e, s_e_list) }
  | LBRACKET RBRACKET
      { nil_desc }
  | LBRACKET l = list_of(SEMI, expression) RBRACKET
      { cons_list_desc l ($startpos($1)) ($endpos($3)) }
  | LAST i = ide
      { Elast(true, i) }
  | LAST_STAR i = ide
      { Elast(false, i) }
  | a = atomic_constant
      { Econst a }
  | LPAREN RPAREN
      { Econst Evoid }
  | LPAREN e = expression_comma_list RPAREN
      { Etuple (List.rev e) }
  | LPAREN e = seq_expression RPAREN
    { e.desc }
  | LBRACE l = label_expression_list RBRACE
      { Erecord(l) }
  | LBRACE e = simple_expression WITH l = label_expression_list RBRACE
    { Erecord_with(e, l) }
  | e = simple_expression DOT i = ext_ident
      { Erecord_access(e, i) }
  | LPAREN e = simple_expression COLON t = type_expression RPAREN
      { Etypeconstraint(e, t) }
  | LBRACKETBAR RBRACKETBAR
    { Eop(Earray(Earray_list), []) }
  | LBRACKETBAR l = list_of(SEMI, expression) RBRACKETBAR
    { Eop(Earray(Earray_list), l) }
  | LBRACKETBAR e1 = simple_expression
    WITH i_list = update_array_comma_list LESSMINUS e2 = expression RBRACKETBAR
    { Eop(Earray(Eupdate), e1 :: e2 :: List.rev i_list) }
  | e1 = simple_expression DOT LPAREN e2 = expression RPAREN
      { Eop(Earray(Eget), [e1; e2]) }
  | e = simple_expression DOT
      LPAREN e1 = expression DOTDOT e2 = expression RPAREN
      { Eop(Earray(Eslice), [e; e1; e2]) }
;

/* size expression list */
size_expression_list:
  | s_list = list_of(COMMA, size_expression)
    { s_list }
;

size_expression:
  | s = localized(size_expression_desc)
    { s }
;

size_expression_desc:
  | i = ide
    { Size_var(i) }
  | i = INT
    { Size_int(i) }
  | num = size_expression DIV denom = INT
    { Size_frac(num, denom) }
  | e1 = size_expression PLUS e2 = size_expression
    { Size_op(Size_plus, e1, e2) }
  | e1 = size_expression MINUS e2 = size_expression
    { Size_op(Size_minus, e1, e2) }
  | e1 = size_expression STAR e2 = size_expression
    { Size_op(Size_mult, e1, e2) }
;

/* [| e with e1,...,en <- e' |] */
/* is a short-cut for [| e with i <- [| e.(i) with j <- e' |] |] */
update_array_comma_list:
  | e = simple_expression
    { [ e ] }
  | l = update_array_comma_list COMMA e = simple_expression
    { e :: l }
;

expression_comma_list:
  | ecl = expression_comma_list COMMA e = expression
      { e :: ecl }
  | e1 = expression COMMA e2 = expression
      { [e2; e1] }
;

expression:
  | x = localized(expression_desc)
    { x }
;

expression_desc:
  | e = simple_expression_desc
      { e }
  | e = expression_comma_list %prec prec_list
      { Etuple(List.rev e) }
  | e1 = simple_expression FBY e2 = expression
      { Eop(Efby, [e1; e2]) }
  | i = is_inline RUN f = simple_expression e = simple_expression
      { Eop(Erun(i), [f; e]) }
  | i = is_inline f = simple_expression arg_list = simple_expression_list
      { app i f arg_list }
  | a = is_atomic k = fun_kind p_list_list = param_list_list
    MINUSGREATER e = expression
    { funexp_desc a k p_list_list (make (Exp(e)) $startpos(e) $endpos)
      $startpos(p_list_list) $endpos }
  | a = is_atomic k = fun_kind p_list_list = param_list_list
    RETURNS p = param eq = equation
    { funexp_desc a k p_list_list (make (Returns(p, eq)) $startpos(p) $endpos)
         $startpos(p_list_list) $endpos }
  | ATOMIC e = simple_expression
    { Eop(Eatomic, [e]) }
  | PRE e = expression
      { Eop(Eunarypre, [e]) }
  | e1 = expression MINUSGREATER e2 = expression %prec prec_minus_greater
      { Eop(Eminusgreater, [e1; e2]) }
  | UP e = expression
      { Eop(Eup, [e]) }
  | TEST e = expression
      { Eop(Etest, [e]) }
  | IF e1 = seq_expression THEN e2 = seq_expression ELSE e3 = seq_expression
      { Eop(Eifthenelse, [e1; e2; e3]) }
  | MINUS e = expression  %prec prec_uminus
      { unary_minus "-" e ($startpos($1)) ($endpos($1)) }
  | s = SUBTRACTIVE e = expression  %prec prec_uminus
      { unary_minus s e ($startpos(s)) ($endpos(s)) }
  | e1 = expression i = INFIX4 e2 = expression
      { binop i e1 e2 ($startpos(i)) ($endpos(i)) }
  | e1 = expression i = INFIX3 e2 = expression
      { binop i e1 e2 ($startpos(i)) ($endpos(i)) }
  | e1 = expression i = INFIX2 e2 = expression
      { binop i e1 e2 ($startpos(i)) ($endpos(i)) }
  | e1 = expression PLUS e2 = expression
      { binop "+" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression i = INFIX1 e2 = expression
      { binop i e1 e2 ($startpos(i)) ($endpos(i)) }
  | e1 = expression i = INFIX0 e2 = expression
      { binop i e1 e2 ($startpos(i)) ($endpos(i)) }
  | e1 = expression LESSER e2 = expression
      { binop "<" e1 e2 $startpos $endpos }
  | e1 = expression GREATER e2 = expression
      { binop ">" e1 e2 $startpos $endpos }
  | e1 = expression EQUAL e2 = expression
      { binop "=" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression OR e2 = expression
      { binop "or" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression STAR e2 = expression
      { binop "*" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression DIV e2 = expression
      { binop "/" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression AMPERSAND e2 = expression
      { binop "&" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression MINUS e2 = expression
      { binop "-" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression s = SUBTRACTIVE e2 = expression
      { binop s e1 e2 ($startpos(s)) ($endpos(s)) }
  | e1 = expression AMPERAMPER e2 = expression
      { binop "&&" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression BARBAR e2 = expression
      { binop "||" e1 e2 ($startpos($2)) ($endpos($2)) }
  | p = PREFIX e = expression
      { unop p e ($startpos(p)) ($endpos(p)) }
  | LET v = vkind_opt i = is_rec eq = equation_and_list IN e = seq_expression
    { Elet(make { l_rec = i; l_kind = v; l_eq = eq } $startpos $endpos(eq), e) }
  | LOCAL v_list = vardec_comma_list DO eq = equation_and_list IN e = seq_expression
    { Elocal(v_list, eq, e) }  
  | MATCH e = seq_expression WITH
      opt_bar m = match_handlers(expression) opt_end
      { Ematch(e, List.rev m) }
  | PRESENT opt_bar pe = present_handlers(expression) opt_end %prec prec_present
    { Epresent(List.rev pe, NoDefault) }
  | PRESENT opt_bar pe = present_handlers(expression)
    INIT e = expression opt_end %prec prec_present
    { Epresent(List.rev pe, Init(e)) }
  | PRESENT opt_bar pe = present_handlers(expression)
    ELSE e = seq_expression opt_end %prec prec_present
      { Epresent(List.rev pe, Else(e)) }
  | RESET e = seq_expression EVERY r = expression
    { Ereset(e, r) }
  | PERIOD p = period_expression
    { Eop(Eperiod, p) }
  | HORIZON e = simple_expression
    { Eop(Ehorizon, [e]) }
  | ASSERT e = simple_expression
    { Eassert(e) }
  | FOREACH f = foreach_loop_exp
    { Eforloop (foreach_loop false f) }
  | FORWARD f = forward_loop_exp
    { Eforloop (forward_loop false f) }
  | FORWARD RESUME f = forward_loop_exp
    { Eforloop (forward_loop true f) }
  | e1 = simple_expression DOT LPAREN e2 = expression RPAREN
    DEFAULT e3 = expression
    { Eop(Earray(Eget_with_default), [e1; e2; e3]) }
  | e1 = expression PLUSPLUS e2 = expression
      { Eop(Earray(Econcat), [e1; e2]) }
  | e = expression TRANSPOSE
      { Eop(Earray(Etranspose), [e]) }
  | e = expression FLATTEN
      { Eop(Earray(Eflatten), [e]) }
  | e = expression REVERSE
      { Eop(Earray(Ereverse), [e]) }
;

%inline opt_end:
/* empty */
    {}
  | END {}
;

/* Loops for equations */
foreach_loop_exp:
  /* foreach (size) [i] (xi in ei,...) do e [default e] */
  | s_opt = optional_size_expression
    i_opt = optional(index)
    li = empty(input_list)
    DO e = expression
    d_opt = optional(default_expression)
    DONE
    { (s_opt, i_opt, li, Forexp { exp = e; default = d_opt }) }
  | /* foreach (size) [i] (xi in ei,...) returns (...) do
       eq done */
    s_opt = optional_size_expression
    i_opt = optional(index)
    li = empty(input_list)
    RETURNS p = for_return
    b = block(equation_empty_and_list)
    DONE
    { (s_opt, i_opt, li, Forreturns { r_returns = p; r_block = b }) }
;

forward_loop_exp:
  /* forward (size) [i] (xi in ei,...) do e [default e] [while/unless/until e] done */
  | s_opt = optional_size_expression
    i_opt = optional(index)
    li = empty(input_list)
    DO e = expression
    d_opt = optional(default_expression)
    o_opt = optional(loop_exit_condition)
    DONE
    { (s_opt, i_opt, li, o_opt, Forexp { exp = e; default = d_opt }) }
  | /* forward (size) [i] (xi in ei,...) returns (...) do
       eq [while/unless/until e] done */
    s_opt = optional_size_expression
    i_opt = optional(index)
    li = empty(input_list)
    RETURNS p = for_return
    b = block(equation_empty_and_list)
    o_opt = optional(loop_exit_condition)
    DONE
    { (s_opt, i_opt, li, o_opt, Forreturns { r_returns = p; r_block = b }) }
;

/* Loops for equations */
foreach_loop_eq:
  s_opt = optional_size_expression i_opt = optional(index)
    li = empty(input_list) RETURNS 
    lo = output_list f = block(equation_empty_and_list)
    DONE
    { (s_opt, i_opt, li, { for_out = lo; for_block = f }) }
;

forward_loop_eq:
  | s_opt = optional_size_expression i_opt = optional(index)
    li = empty(input_list) RETURNS 
    lo = output_list 
    f = block(equation_empty_and_list)
    o_opt = optional(loop_exit_condition)
    DONE
    { (s_opt, i_opt, li, o_opt, { for_out = lo; for_block = f }) }
;

%inline optional_size_expression:
  | { None }
  | LPAREN e = expression RPAREN { Some(e) }
;

index:
  | LBRACKET i = ide RBRACKET { i }
;

/* input in a for loop */
input_list:
  | LPAREN l = list_of(COMMA, localized(input_desc)) RPAREN { l }
  | l = list_of(COMMA, localized(input_desc)) { l }
;

input_desc:
  | i = ide IN e = expression o = optional(by_expression) %prec prec_in_input
    { Einput { id = i; e = e; by = o } }
  | i = ide IN e1 = expression TO e2 = expression
    { Eindex { id = i; e_left = e1; e_right = e2; dir = true } }
  | i = ide IN e1 = expression DOWNTO e2 = expression
    { Eindex { id = i; e_left = e1; e_right = e2; dir = false } }
;

by_expression:
  | BY e = simple_expression
    { e }
;

loop_exit_condition:
  | k = loop_exit_condition_kind e = expression
    { { for_exit_kind = k; for_exit = e } }
;

loop_exit_condition_kind:
| WHILE { Ewhile }
| UNTIL { Euntil }
| UNLESS { Eunless }
;

/* outputs of a loop */
output_list:
  | LPAREN l = list_of(COMMA, localized(output_desc)) RPAREN { l }
;

out_ide:
  | OUT ide = ide
    { ide }
;

output_desc:
  /* xi */
  | ide = ide
    { { for_name = ide; for_out_name = None;
        for_init = None; for_default = None } }
  /* xi out x */
  | ide = ide o = out_ide 
    { { for_name = ide; for_out_name = Some(o);
	for_init = None; for_default = None } }
  /* xi init e [out x] */
  | ide = ide i = init_expression o_opt = optional(out_ide)
    { { for_name = ide; for_out_name = o_opt;
	for_init = Some(i); for_default = None } }
  /* xi default e [out x] */
  | ide = ide d = default_expression o_opt = optional(out_ide)
    { { for_name = ide; for_out_name = o_opt;
	for_init = None; for_default = Some(d) } }
  /* xi init e default e [out x] */
  | ide = ide i = init_expression d = default_expression 
  o_opt = optional(out_ide)
    { { for_name = ide; for_out_name = o_opt;
	for_init = Some(i); for_default = Some(d) } }
;

/* Periods */
period_expression:
  | LPAREN per = expression RPAREN /* period */
      { [ make (Econst(Efloat(0.0))) $startpos $endpos; per ] }
  | LPAREN ph = simple_expression BAR per = expression RPAREN /* period */
      { [ ph; per ] }
;

%inline is_inline:
  | { false }
  | INLINE { true }
;

%inline is_rec:
  | REC { true }
  |     { false }
;
constructor:
  | c = CONSTRUCTOR %prec prec_ident
      { Name(c) }
  | c1 = CONSTRUCTOR DOT c2 = CONSTRUCTOR
      { Modname({qual = c1; id = c2}) }
;

qual_ident:
  | c = CONSTRUCTOR DOT i = ide
      { {qual = c; id = i} }
;

/* Constants */
atomic_constant:
  | i = INT
      { Eint(i) }
  | f = FLOAT
      { Efloat(f) }
  | s = STRING
      { Estring s }
  | c = CHAR
      { Echar c }
  | b = BOOL
      { Ebool b }
;

/* labels */
label_expression_list:
  | l = label_expression
      { [l] }
  | l = label_expression SEMI
      { [l] }
  | l = label_expression SEMI ll = label_expression_list
      { l :: ll }

label_expression:
  | i = ext_ident EQUAL e = expression
      { (i, e) }
;

/* identifiers */
ide:
  | i = IDENT
      { i }
  | LPAREN i = infx RPAREN
      { i }
;

ext_ident :
  | q = qual_ident
      { Modname(q) }
  | i = ide
      { Name(i) }
;

infx:
  | INFIX0          { $1 }
  | INFIX1          { $1 }    | INFIX2        { $1 }
  | INFIX3          { $1 }    | INFIX4        { $1 }
  | STAR            { "*" }
  | PLUS            { "+" }
  | DIV             { "/" }
  | MINUS           { "-" }
  | GREATER         { ">" }
  | LESSER          { "<" }
  | EQUAL           { "=" }
  | EQUALEQUAL      { "==" }
  | SUBTRACTIVE     { $1 }    | PREFIX        { $1 }
  | AMPERSAND       { "&" }   | AMPERAMPER    { "&&" }
  | OR              { "or" }  | BARBAR        { "||" }
  | ON              { "on" }
;


/* Type expressions */
type_expression:
  | t = simple_type
      { t }
  | tl = type_star_list
      { make(Etypetuple(List.rev tl)) $startpos $endpos}
  | t_arg = type_expression a = arrow t_res = type_expression
      { make(Etypefun(a, None, t_arg, t_res)) $startpos $endpos}
  | LPAREN id = IDENT COLON t_arg = type_expression RPAREN
			    a = arrow t_res = type_expression
      { make(Etypefun(a, Some(id), t_arg, t_res)) $startpos $endpos}
;

simple_type:
  | t = type_var
      { make (Etypevar t) $startpos $endpos }
  | i = ext_ident
      { make (Etypeconstr(i, [])) $startpos $endpos }
  | t = simple_type i = ext_ident
      { make (Etypeconstr(i, [t])) $startpos $endpos }
  | LPAREN t = type_expression COMMA tl = type_comma_list RPAREN i = ext_ident
      { make (Etypeconstr(i, t :: tl)) $startpos $endpos }
  | t_arg = simple_type LBRACKET s = size_expression RBRACKET
      { make(Etypevec(t_arg, s)) $startpos $endpos}
  | LPAREN t = type_expression RPAREN
      { t }
;

type_star_list:
  | t1 = simple_type STAR t2 = simple_type
      { [t2; t1] }
  | tsl = type_star_list STAR t = simple_type
      { t :: tsl }
;

type_var :
  | QUOTE i = IDENT
      { i }
;

type_comma_list :
  | te = type_expression COMMA tl = type_comma_list
      { te :: tl }
  | te = type_expression
      { [te] }
;

%inline arrow:
  | MINUSGREATER
      { Kfun(Kany) }
  | VFUN
       { Kfun(Kconst) }
  | SFUN
       { Kfun(Kstatic) }
  | AFUN
       { Kfun(Kany) }
  | DFUN
       { Knode(Kdiscrete) }
  | CFUN
       { Knode(Kcont) }
;
