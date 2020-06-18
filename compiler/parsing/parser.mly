(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
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
  Eapp({ app_inline = false; app_statefull = false},
       make_name op start_pos end_pos, [e])
let binop op e1 e2 start_pos end_pos =
  Eapp({ app_inline = false; app_statefull = false},
       make_name op start_pos end_pos, [e1; e2])

let unary_minus op e start_pos end_pos =
  match op, e.desc with
    | "-", Econst(Eint v) -> Econst(Eint(-v))
    | ("-" | "_."), Econst(Efloat v) -> Econst(Efloat(-.v))
    | _ -> unop ("~" ^ op) e start_pos end_pos

let unary_minus_int x = -x
and unary_minus_float x = -.x

(* Representation of lists. [] for Pervasives.[] *)
(* [e1;...;en] for Pervasives.(::) e1 (... Pervasives.[]) *)
let list_name n = Modname { qual = Initial.stdlib_module; id = n }

let nil_desc = Evar(list_name Initial.nil_name)

let cons_desc x l start_pos end_pos =
  Eapp({ app_inline = false; app_statefull = false },
       make (Evar(list_name Initial.cons_name)) start_pos end_pos,
       [make (Etuple [x; l]) start_pos end_pos])

let rec cons_list_desc l start_pos end_pos =
  match l with
  | [] -> nil_desc
  | x :: l -> cons_desc x (cons_list l start_pos end_pos) start_pos end_pos

and cons_list l start_pos end_pos =
  make (cons_list_desc l start_pos end_pos) start_pos end_pos

let scond_true start_pos end_pos =
  make (Econdexp(make (Econst(Ebool(true))) start_pos end_pos))
       start_pos end_pos

(* constructors with arguments *)
let app f l =
  match f.desc, l with
  | Econstr0(id), [{ desc = Etuple(arg_list) }] ->
    (* C(e1,...,en) *) Econstr1(id, arg_list)
  | Econstr0(id), [arg] ->
     (* C(e) *) Econstr1(id, [arg])
  | _ -> Eapp({ app_inline = false; app_statefull = false}, f, l)

let constr c p =
   match p with
  | { desc = Etuplepat(arg_list) } ->
    (* C(p1,...,pn) *) Econstr1pat(c, arg_list)
  | _ -> (* C(e) *) Econstr1pat(c, [p])

let block l lo eq_list startpos endpos =
  make { b_locals = l; b_vars = lo; b_body = eq_list } startpos endpos

%}

%token EQUAL          /* "=" */
%token EQUALEQUAL     /* "==" */
%token PLUSEQUAL      /* "+=" */
%token AMPERSAND      /* "&" */
%token AMPERAMPER     /* "&&" */
%token BARBAR         /* "||" */
%token QUOTE          /* "'" */
%token LPAREN         /* "(" */
%token RPAREN         /* ")" */
%token LBRACKET       /* "[" */
%token RBRACKET       /* "]" */
%token STAR           /* "*" */
%token PLUS           /* "+" */
%token MINUS          /* "-" */
%token COMMA          /* "," */
%token SEMI           /* ";" */
%token SEMISEMI       /* ";;" */
%token MINUSGREATER   /* "->" */
%token AFUN           /* "-A->" */
%token ADFUN          /* "-AD->" */
%token ASFUN          /* "-AS->" */
%token DFUN           /* "-D->" */
%token CFUN           /* "-C->" */
%token SFUN           /* "-S->" */
%token PFUN           /* "~D~>" */
%token DOT            /* "." */
%token DOTDOT         /* ".." */
%token COLON          /* ":" */
%token COLONCOLON     /* "::" */
%token LBRACE         /* "{" */
%token BAR            /* "|" */
%token RBRACE         /* "}" */
%token LBRACKETBAR    /* "[|" */
%token RBRACKETBAR    /* "|]" */
%token UNDERSCORE     /* "_" */
%token TEST           /* "?" */
%token <string> CONSTRUCTOR
%token <string> IDENT
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token <char> CHAR
%token <string> STRING
%token AS             /* "as" */
%token FORALL         /* "forall" */
%token AUTOMATON      /* "automaton" */
%token ATOMIC         /* "atomic" */
%token INLINE         /* "inline" */
%token CONTINUE       /* "continue" */
%token DO             /* "do" */
%token DONE           /* "done" */
%token UNTIL          /* "until" */
%token UNLESS         /* "unless" */
%token MATCH          /* "match" */
%token WITH           /* "with" */
%token EMIT           /* "emit" */
%token PRESENT        /* "present" */
%token PERIOD         /* "period" */
%token END            /* "end" */
%token EXCEPTION      /* "exception" */
%token EXTERNAL       /* "external" */
%token IN             /* "in" */
%token BEFORE         /* "before" */
%token OUT            /* "out" */
%token LET            /* "let" */
%token REC            /* "rec" */
%token DER            /* "der" */
%token INIT           /* "init" */
%token INITIALIZE     /* "initialize" */
%token DEFAULT        /* "default" */
%token LOCAL          /* "local" */
%token WHERE          /* "where" */
%token AND            /* "and" */
%token TYPE           /* "type" */
%token STATIC         /* "static" */
%token OF             /* "of" */
%token FUN            /* "fun" */
%token NODE           /* "node" */
%token HYBRID         /* "hybrid" */
%token PROBA          /* "proba" */
%token DISCRETE       /* "discrete" */
%token FBY            /* "fby" */
%token NEXT           /* "next" */
%token PRE            /* "pre" */
%token UP             /* "up" */
%token DISC           /* "disc" */
%token EVERY          /* "every" */
%token OR             /* "or" */
%token ON             /* "on" */
%token RESET          /* "reset" */
%token LAST           /* "last" */
%token IF             /* "if" */
%token THEN           /* "then" */
%token ELSE           /* "else" */
%token OPEN           /* "open" */
%token VAL            /* "val" */
%token RUN            /* "run" */
%token <string> PREFIX
%token <string> INFIX0
%token <string> INFIX1
%token <string> INFIX2
%token <string> SUBTRACTIVE
%token <string> INFIX3
%token <string> INFIX4
%token EOF

%nonassoc prec_no_end
%nonassoc END
%right IN
%right prec_seq
%right SEMI
%nonassoc prec_ident
%right prec_list
%left EVERY
%left AUTOMATON
%left INIT
%left UNTIL
%left UNLESS
%nonassoc ELSE
%right BEFORE
%left  AS
%left  BAR
%left COMMA
%left RPAREN
%right MINUSGREATER SFUN DFUN CFUN AFUN ADFUN ASFUN PFUN
%left OR BARBAR
%left AMPERSAND AMPERAMPER
%left INFIX0 EQUAL
%right INFIX1
%right COLONCOLON
%left INFIX2 PLUS SUBTRACTIVE MINUS
%left STAR INFIX3
%left ON
%left INFIX4
%right prec_uminus
%right FBY
%right PRE UP DISC TEST ATOMIC
%right PREFIX
%left DOT

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

/* Non separated list */
list_aux_no_sep(X):
| x = X { [x] }
| r = list_aux_no_sep(X) x = X { x :: r }
;

%inline list_no_sep_of(X):
   r = list_aux_no_sep(X) { List.rev r }
;

/* Localization */
localized(X):
| x = X { make x $startpos $endpos }
;

%inline optional(X):
  | /* empty */
      { None }
  | x = X
      { Some(x) }
;

implementation_file:
  | EOF
      { [] }
  | i = decl_list(localized(implementation)) EOF
      { List.rev i }
;

decl_list(X):
  | dl = decl_list(X) x = X opt_semi_semi
      { x :: dl }
  | x = X opt_semi_semi
      { [x] }
;

opt_semi_semi:
  | /* empty */ {}
  | SEMISEMI {}
;

implementation:
  | OPEN c = CONSTRUCTOR
      { Eopen c }
  | TYPE tp = type_params id = IDENT td = localized(type_declaration_desc)
      { Etypedecl(id, tp, td) }
  | LET ide = ide EQUAL seq = seq_expression
      { Econstdecl(ide, false, seq) }
  | LET STATIC ide = ide EQUAL seq = seq_expression
      { Econstdecl(ide, true, seq) }
  | LET ide = ide fn = simple_pattern_list EQUAL seq = seq_expression
      { Efundecl(ide, { f_kind = A; f_atomic = false;
			f_args = fn; f_body = seq;
			f_loc = localise $startpos(fn) $endpos(seq) }) }
  | LET ide = ide fn = simple_pattern_list EQUAL
	seq = seq_expression WHERE r = is_rec eqs = equation_list
      { Efundecl(ide, { f_kind = A; f_atomic = false; f_args = fn;
			f_body = make(Elet(r, eqs, seq))
				 $startpos(seq) $endpos(eqs);
		       f_loc = localise $startpos(fn) $endpos(eqs) }) }
  | is_let a = is_atomic k = kind ide = ide fn = simple_pattern_list
					EQUAL seq = seq_expression
      { Efundecl(ide,
		 { f_kind = k; f_atomic = a; f_args = fn; f_body = seq;
		  f_loc = localise $startpos(fn) $endpos(seq) }) }
  | is_let a = is_atomic k = kind ide = ide
	  fn = simple_pattern_list EQUAL seq = seq_expression
          WHERE r = is_rec eqs = equation_list
      { Efundecl(ide, { f_kind = k; f_atomic = a; f_args = fn;
			f_body = make(Elet(r, eqs, seq))
				 $startpos(seq) $endpos(eqs);
			f_loc = localise $startpos(fn) $endpos(eqs) }) }
;

%inline is_rec:
  | REC { true }
  |     { false }
;

%inline is_atomic:
  | ATOMIC { true }
  | { false }
;

%inline is_let:
  | LET { }
  | { }
;

simple_pattern_list:
  | p = simple_pattern
	  { [ p ] }
  | p = simple_pattern sp = simple_pattern_list
     { p :: sp }
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
  | TYPE tp = type_params i = IDENT td = localized(type_declaration_desc)
      { Einter_typedecl(i, tp, td) }
  | VAL i = ide COLON t = type_expression
      { Einter_constdecl(i, t) }
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
      { [make (Einter_typedecl(i, tp, td)) $startpos $endpos] }
  | VAL i = ide COLON t = type_expression
      { [make (Einter_constdecl(i, t)) $startpos $endpos] }
  | EXTERNAL i = ide COLON t = type_expression EQUAL list_no_sep_of(STRING)
      { [make (Einter_constdecl(i, t)) $startpos $endpos] }
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

equation_empty_list:
  | /* empty */
      { [] }
  | eq_list = equation_list
      { eq_list }
;

optional_init:
  | /* empty */
      { None }
  | INIT e = expression
      { Some(e) }
;

%inline equation_list:
  | l = list_of(AND, equation) { l }
;

%inline equation:
   eq = localized(equation_desc) { eq }
;

equation_desc:
  | AUTOMATON opt_bar a = automaton_handlers(equation_empty_list) opt_end
    { EQautomaton(List.rev a, None) }
  | AUTOMATON opt_bar a = automaton_handlers(equation_empty_list)
    INIT s = state
    { EQautomaton(List.rev a, Some(s)) }
  | MATCH e = seq_expression WITH opt_bar
    m = match_handlers(block_of_equation_list) opt_end
    { EQmatch(e, List.rev m) }
  | IF e = seq_expression THEN b1 = block_of_equation_list
    ELSE b2 = block_of_equation_list opt_end
    { EQifthenelse(e, b1, Some b2) }
  | IF e = seq_expression THEN b1 = block_of_equation_list
      { EQifthenelse(e, b1, None) }
  | PRESENT opt_bar p = present_handlers(block_of_equation_list) opt_end
    { EQpresent(List.rev p, None) }
  | PRESENT opt_bar p = present_handlers(block_of_equation_list)
    ELSE b = block_of_equation_list opt_end
    { EQpresent(List.rev p, Some(b)) }
  | RESET eq = equation_list EVERY e = expression
    { EQreset(eq, e) }
  | l = let_list lo = local_list DO eq_list = equation_empty_list DONE
    { EQblock(block l lo eq_list $startpos $endpos) }
  | FORALL i = index_list bo = block(equation_list)
    INITIALIZE inits = init_equation_list DONE
    { EQforall
	{ for_indexes = i; for_init = inits; for_body = bo } }
  | FORALL i = index_list  bo = block(equation_list) DONE
    { EQforall
	{ for_indexes = i; for_init = []; for_body = bo } }
  | p = pattern EQUAL e = seq_expression
    { EQeq(p, e) }
  | i = ide PLUSEQUAL e = seq_expression
    { EQpluseq(i, e) }
  | PERIOD p = pattern EQUAL e = period_expression
    { EQeq(p, make (Eperiod(e)) $startpos(e) $endpos(e)) }
  | DER i = ide EQUAL e = seq_expression opt = optional_init
      { EQder(i, e, opt, []) }
  | DER i = ide EQUAL e = seq_expression opt = optional_init
    RESET opt_bar pe = present_handlers(expression)
      { EQder(i, e, opt, List.rev pe) }
  | NEXT i = ide EQUAL e = seq_expression
      { EQnext(i, e, None) }
  | NEXT i = ide EQUAL e = seq_expression INIT e0 = seq_expression
      { EQnext(i, e, Some(e0)) }
  | INIT i = ide EQUAL e = seq_expression
      { EQinit(i, e) }
  | EMIT i = ide
      { EQemit(i, None) }
  | EMIT i = ide EQUAL e = seq_expression
      { EQemit(i, Some(e)) }
  | eq1 = equation BEFORE eq2 = equation
      { EQbefore [eq1; eq2] }
;

opt_end:
  | { () } %prec prec_no_end
  | END { () }
;

%inline simple_equation:
   eq = localized(simple_equation_desc) { eq }
;

simple_equation_desc:
  | AUTOMATON opt_bar a = automaton_handlers(equation_empty_list) END
    { EQautomaton(List.rev a, None) }
  | AUTOMATON opt_bar a = automaton_handlers(equation_empty_list)
    INIT s = state
    { EQautomaton(List.rev a, Some(s)) }
  | MATCH e = seq_expression WITH opt_bar
    m = match_handlers(block_of_equation_list) END
    { EQmatch(e, List.rev m) }
  | PRESENT opt_bar p = present_handlers(block_of_equation_list) END
    { EQpresent(List.rev p, None) }
  | PRESENT opt_bar p = present_handlers(block_of_equation_list)
    ELSE b = block_of_equation_list END
    { EQpresent(List.rev p, Some(b)) }
  | RESET eq = equation_list EVERY e = expression
    { EQreset(eq, e) }
  | FORALL i = index_list bo = block(equation_list)
    INITIALIZE inits = init_equation_list DONE
    { EQforall
	{ for_indexes = i; for_init = inits; for_body = bo } }
  | FORALL i = index_list  bo = block(equation_list) DONE
    { EQforall
	{ for_indexes = i; for_init = []; for_body = bo } }
;
    
/* initialization in a for loop */
%inline init_equation_list:
  | l = list_of(AND, localized(init_equation_desc)) { l }
;

init_equation_desc:
  | LAST i = ide EQUAL e = expression
     { Einit_last(i, e) }
  ;

/* indexes in a for loop */
%inline index_list:
  | l = list_of(COMMA, localized(index_desc)) { l }
;

index_desc:
  | i = ide IN e = simple_expression
     { Einput(i, e) }
  | i = ide OUT o = ide
     { Eoutput(i, o) }
  | i = ide IN e1 = simple_expression DOTDOT e2 = simple_expression
     { Eindex(i, e1, e2) }
;


/* states of an automaton in an equation*/
automaton_handlers(X) :
  | a = automaton_handler(X)
      { [a] }
  | ahs = automaton_handlers(X) BAR a = automaton_handler(X)
      { a :: ahs }
;

automaton_handler(X):
  | sp = state_pat MINUSGREATER b = block(X) DONE
     { make { s_state = sp; s_block = b; s_until = []; s_unless = [] }
            $startpos $endpos}
  | sp = state_pat MINUSGREATER b = block(X) THEN st = state
    { make { s_state = sp; s_block = b;
             s_until =
               [{ e_cond = scond_true $endpos(b) $startpos(st);
                  e_reset = true; e_block = None; e_next_state = st }];
	   s_unless = [] }
      $startpos $endpos}
  | sp = state_pat MINUSGREATER b = block(X) CONTINUE st = state
    { make { s_state = sp;
             s_block = b;
             s_until =
               [{ e_cond = scond_true $endpos(b) $startpos(st);
                  e_reset = false;
                  e_block = None; e_next_state = st }];
	     s_unless = [] } $startpos $endpos }
  | sp = state_pat MINUSGREATER b = block(X) THEN emit = emission st = state
    { make { s_state = sp; s_block = b;
             s_until =
               [{ e_cond = scond_true $endpos(b) $startpos(emit);
                  e_reset = true; e_block = Some(emit); e_next_state = st}];
	     s_unless = [] } $startpos $endpos }
  | sp = state_pat MINUSGREATER b = block(X) CONTINUE emit = emission
    st = state
    { make { s_state = sp;
             s_block = b;
             s_until = [{ e_cond = scond_true $endpos(b) $startpos(emit);
                          e_reset = false; e_block = Some(emit);
                          e_next_state = st}];
	     s_unless = [] } $startpos $endpos }
  | sp = state_pat MINUSGREATER b = block(X) UNTIL e_until = escape_list
    { make
       { s_state = sp; s_block = b; s_until = List.rev e_until; s_unless = [] }
       $startpos $endpos }
  | sp = state_pat MINUSGREATER b = block(X) UNLESS e_unless = escape_list
    { make
       { s_state = sp; s_block = b; s_until = []; s_unless = List.rev e_unless }
      $startpos $endpos }
  | sp = state_pat MINUSGREATER b = block(X) UNTIL e_until = escape_list
					     UNLESS e_unless = escape_list
    { make { s_state = sp; s_block = b;
	     s_until = List.rev e_until; s_unless = List.rev e_unless }
      $startpos $endpos }
;

escape :
  | scondpat THEN state
      { { e_cond = $1; e_reset = true; e_block = None; e_next_state = $3 } }
  | scondpat CONTINUE state
      { { e_cond = $1; e_reset = false; e_block = None; e_next_state = $3 } }
  | scondpat THEN emission state
      { { e_cond = $1; e_reset = true; e_block = Some($3); e_next_state = $4 } }
  | scondpat CONTINUE emission state
      { { e_cond = $1; e_reset = false; e_block = Some($3); e_next_state = $4 } }
;

escape_list :
  | e = escape
      { [e] }
  | el = escape_list ELSE e = escape
      { e :: el }
;

state :
  | c = CONSTRUCTOR
      { make (Estate0(c)) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN e = expression RPAREN
      { make (Estate1(c, [e])) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN l = expression_comma_list RPAREN
      { make (Estate1(c, List.rev l)) $startpos $endpos }
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
  | UP e = simple_expression
      { Econdexp (make (Eop(Eup, [e])) $startpos $endpos) }
  | scpat1 = scondpat AMPERSAND scpat2 = scondpat
      { Econdand(scpat1, scpat2) }
  | scpat1 = scondpat BAR scpat2 = scondpat
      { Econdor(scpat1, scpat2) }
  | scpat1 = scondpat ON e = simple_expression
      { Econdon(scpat1, e) }
;

/* Block */
block(X):
  | l = let_list lo = local_list DO x = X
      { make { b_locals = l; b_vars = lo; b_body = x } $startpos $endpos }
;

block_of_equation_list:
  | eq = simple_equation
      { block [] [] [eq] $startpos $endpos }
  | l = let_list lo = local_list DO eq_list = equation_empty_list DONE
      { block l lo eq_list $startpos $endpos }
;


emission:
  | l1 = one_let IN l2 = let_list
    { make { b_vars = []; b_locals = l1 :: l2; b_body = [] } $startpos $endpos }
  | l = let_list lo = local_list DO eq = equation_empty_list IN
      { make { b_vars = lo; b_locals = l; b_body = eq } $startpos $endpos }
;

let_list:
  | /* empty */
      { [] }
  | o = one_let IN l = let_list
      { o :: l }
;

one_let:
  | LET eq = equation_list
      { make (false, eq) $startpos $endpos }
  | LET REC eq = equation_list
      { make (true, eq) $startpos $endpos }
;

local_list:
  | /* empty */
      { [] }
  | LOCAL o = list_of(COMMA, one_local) opt_in l = local_list
      { o @ l }
;

opt_in:
    /* epsilon */
  | {}
  | IN { () }
;

one_local:
  | i = ide v = optional(default_or_init) c = opt_combine
    { make { vardec_name = i; vardec_default = v; vardec_combine = c }
	$startpos $endpos }
;

default_or_init:
  | DEFAULT c = constant
      { Default(c) }
  | INIT c = constant
    { Init(c) }
;

opt_combine:
  | /* empty */
      { None }
  | WITH i = ext_ident
    { Some(i) }
;

constant:
  | i = atomic_constant
    { Cimmediate(i) }
  | i = ext_ident
    { Cglobal(i) }
;


opt_bar:
  | BAR             { () }
  | /*epsilon*/     { () }
;


/* Testing the presence of a signals */
present_handlers(X):
  | p = present_handler(X)
      { [p ] }
  | ps = present_handlers(X) BAR p = present_handler(X)
      { p :: ps }
;

present_handler(X):
  | sc = scondpat MINUSGREATER x = X
      { { p_cond = sc; p_body = x } }
;

/* Pattern matching in an equation */
match_handlers(X):
  | m = match_handler(X)
      { [m ] }
  | mh = match_handlers(X) BAR m = match_handler(X)
      { m :: mh }
;

match_handler(X):
  | p = pattern MINUSGREATER x = X
      { { m_pat = p; m_body = x } }
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
      { make (constr c p) $startpos $endpos }
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
      { make (Eseq(e, seq)) $startpos $endpos }
  | e = expression %prec prec_seq
      { e }
;

simple_expression:
  | desc = simple_expression_desc
      { make desc $startpos $endpos }
;

simple_expression_desc:
  | c = constructor
      { Econstr0(c) }
  | i = ext_ident
      { Evar i }
  | LBRACKET RBRACKET
      { nil_desc }
  | LBRACKET l = list_of(SEMI, expression) RBRACKET
      { cons_list_desc l ($startpos($1)) ($endpos($3)) }
  | LAST i = ide
      { Elast(i) }
  | a = atomic_constant
      { Econst a }
  | LBRACE l = label_expression_list RBRACE
      { Erecord(l) }
  | LBRACE e = simple_expression WITH l = label_expression_list RBRACE
      { Erecord_with(e, l) }
  | LPAREN RPAREN
      { Econst Evoid }
  | LPAREN e = expression_comma_list RPAREN
      { Etuple (List.rev e) }
  | LPAREN e = seq_expression RPAREN
      { e.desc }
  | LPAREN e = simple_expression COLON t = type_expression RPAREN
      { Etypeconstraint(e, t) }
  | e = simple_expression DOT i = ext_ident
      { Erecord_access(e, i) }
  | LBRACKETBAR e1 = simple_expression BAR e2 = simple_expression RBRACKETBAR
      { Eop(Econcat, [e1; e2]) }
  | LBRACKETBAR e1 = simple_expression WITH i = simple_expression
					     EQUAL e2 = expression RBRACKETBAR
      { Eop(Eupdate, [e1; i; e2]) }
;

simple_expression_list :
  | e = simple_expression
	  { [e] }
  | l = simple_expression_list e = simple_expression
	  { e :: l }
  ;

expression_comma_list :
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
  | e1 = simple_expression COLONCOLON e2 = expression
      { cons_desc e1 e2 ($startpos(e1)) ($endpos(e2)) }
  | e1 = expression FBY e2 = expression
      { Eop(Efby, [e1; e2]) }
  | f = simple_expression l = simple_expression_list
      {  app f (List.rev l) }
  | INLINE f = simple_expression l = simple_expression_list
      {  Eapp({ app_inline = true; app_statefull = false}, f, List.rev l) }
  | RUN f = simple_expression l = simple_expression_list
      {  Eapp({ app_inline = false; app_statefull = true}, f, List.rev l) }
  | INLINE RUN f = simple_expression l = simple_expression_list
      {  Eapp({ app_inline = true; app_statefull = true}, f, List.rev l) }
  /* | RUN f = simple_expression e = simple_expression  { Eop(Erun, [f; e]) } */
  | ATOMIC e = expression
      { Eop(Eatomic, [e]) }
  | PRE e = expression
      { Eop(Eunarypre, [e]) }
  | INIT
      { Eop(Einitial, []) }
  | UP e = expression
      { Eop(Eup, [e]) }
  | TEST e = expression
      { Eop(Etest, [e]) }
  | DISC e = expression
      { Eop(Edisc, [e]) }
  | IF e1 = seq_expression THEN e2 = seq_expression ELSE e3 = expression
      { Eop(Eifthenelse, [e1; e2; e3]) }
  | e1 = expression MINUSGREATER e2 = expression
      { Eop(Eminusgreater, [e1; e2]) }
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
  | e1 = expression EQUAL e2 = expression
      { binop "=" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression OR e2 = expression
      { binop "or" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression STAR e2 = expression
      { binop "*" e1 e2 ($startpos($2)) ($endpos($2)) }
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
  | e = simple_expression
          LBRACE s1 = size_expression DOTDOT s2 = size_expression RBRACE
      { Eop(Eslice(s1, s2), [e]) }
  | e1 = simple_expression DOT LPAREN e2 = expression RPAREN
      { Eop(Eaccess, [e1; e2]) }
  | LET defs = equation_list IN e = seq_expression
      { Elet(false, defs, e) }
  | LET REC defs = equation_list IN e = seq_expression
      { Elet(true, defs, e) }
  | PERIOD p = period_expression
      { Eperiod(p) }
  | AUTOMATON opt_bar a = automaton_handlers(seq_expression)
      { Eautomaton(List.rev a, None) }
  | AUTOMATON opt_bar a = automaton_handlers(seq_expression) INIT s = state
      { Eautomaton(List.rev a, Some(s)) }
  | MATCH e = seq_expression WITH opt_bar m = match_handlers(expression) opt_end
      { Ematch(e, List.rev m) }
  | PRESENT opt_bar pe = present_handlers(expression) opt_end
      { Epresent(List.rev pe, None) }
  | PRESENT opt_bar pe = present_handlers(expression) INIT e = expression
      { Epresent(List.rev pe, Some(Init(e))) }
  | PRESENT opt_bar pe = present_handlers(expression) ELSE e = seq_expression opt_end
      { Epresent(List.rev pe, Some(Default(e))) }
  | RESET e = seq_expression EVERY r = expression
      { Ereset(e, r) }
  | lo = local_list DO eqs = equation_list IN r = expression
      { Eblock(make { b_locals = []; b_vars = lo; b_body = eqs }
	       $startpos $endpos, r) }
;

/* Periods */
period_expression:
  | LPAREN per = expression RPAREN /* period */
      { { p_phase = None; p_period = per } }
  | LPAREN ph = expression BAR per = expression RPAREN /* period */
      { { p_phase = Some(ph); p_period = per } }
;

constructor:
  | c = CONSTRUCTOR
      { Name(c) } %prec prec_ident
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
  | MINUS           { "-" }
  | EQUAL           { "=" }
  | EQUALEQUAL      { "==" }
  | SUBTRACTIVE     { $1 }    | PREFIX        { $1 }
  | AMPERSAND       { "&" }   | AMPERAMPER    { "&&" }
  | OR              { "or" }  | BARBAR        { "||" }
  | ON              { "on" }
;

%inline arrow:
  | MINUSGREATER
      { Parsetree.A }
  | AFUN
      { Parsetree.A }
  | ADFUN
      { Parsetree.AD }
  | DFUN
      { Parsetree.D }
  | CFUN
      { Parsetree.C }
  | SFUN
      { Parsetree.S }
  | ASFUN
      { Parsetree.AS }
  | PFUN
      { Parsetree.P }
;

size_expression:
    s = localized(size_expression_desc) { s }
;

size_expression_desc:
  | v = INT
     { Sconst(v)  }
  | s = ext_ident
     { Sname(s) }
  | s1 = size_expression PLUS s2 = size_expression
     { Sop(Splus, s1, s2) }
  | s1 = size_expression MINUS s2 = size_expression
     { Sop(Sminus, s1, s2) }
;

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

%inline kind:
  | NODE
      { D }
  | HYBRID
      { C }
  | DISCRETE
      { AD }
  | FUN
      { A }
  | STATIC
      { S }
  | PROBA
      { P }
;
