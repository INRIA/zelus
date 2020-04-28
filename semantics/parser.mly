%{

open Lexing
open Location
open Parsetree

let localise start_pos end_pos = Loc(start_pos.pos_cnum, end_pos.pos_cnum)

let make desc start_pos end_pos =
  { desc = desc; loc = localise start_pos end_pos }

let make_name op start_pos end_pos =
  make (Evar(Name(op))) start_pos end_pos

let unop op e start_pos end_pos = Eapp(Name(op), [e])
let binop op e1 e2 start_pos end_pos = Eapp(Name(op), [e1; e2])

let unary_minus op e start_pos end_pos =
  match op, e.desc with
    | "-", Econst(Eint v) -> Econst(Eint(-v))
    | ("-" | "_."), Econst(Efloat v) -> Econst(Efloat(-.v))
    | _ -> unop ("~" ^ op) e start_pos end_pos

let unary_minus_int x = -x
and unary_minus_float x = -.x

let no_eq start_pos end_pos = make (EQempty) start_pos end_pos

(* constructors with arguments *)
let app f l = Eapp(f, l)

let constr f e =
  match e.desc with
  | Etuple(arg_list) ->
    (* C(e1,...,en) *) Econstr1(f, arg_list)
  | _ ->
     (* C(e) *) Econstr1(id, [e])

let constr_pat c p =
   match p with
  | { desc = Etuplepat(arg_list) } ->
    (* C(p1,...,pn) *) Econstr1pat(c, arg_list)
  | _ -> (* C(e) *) Econstr1pat(c, [p])

let block l lo eq_list startpos endpos =
  make { b_locals = l; b_vars = lo; b_body = eq_list } startpos endpos

%}

%token EQUAL          /* "=" */
%token EQUALEQUAL     /* "==" */
%token AMPERSAND      /* "&" */
%token AMPERAMPER     /* "&&" */
%token BARBAR         /* "||" */
%token LPAREN         /* "(" */
%token RPAREN         /* ")" */
%token STAR           /* "*" */
%token PLUS           /* "+" */
%token MINUS          /* "-" */
%token COMMA          /* "," */
%token MINUSGREATER   /* "->" */
%token BAR            /* "|" */
%token <string> CONSTRUCTOR
%token <string> IDENT
%token <int> INT
%token <float> FLOAT
%token <bool> BOOL
%token RETURNS        /* "returns" */
%token AUTOMATON      /* "automaton" */
%token ATOMIC         /* "atomic" */
%token CONTINUE       /* "continue" */
%token DO             /* "do" */
%token DONE           /* "done" */
%token UNTIL          /* "until" */
%token UNLESS         /* "unless" */
%token MATCH          /* "match" */
%token WITH           /* "with" */
%token END            /* "end" */
%token LET            /* "let" */
%token REC            /* "rec" */
%token IN             /* "in" */
%token INIT           /* "init" */
%token DEFAULT        /* "default" */
%token LOCAL          /* "local" */
%token AND            /* "and" */
%token FUN            /* "fun" */
%token NODE           /* "node" */
%token FBY            /* "fby" */
%token PRE            /* "pre" */
%token EVERY          /* "every" */
%token OR             /* "or" */
%token RESET          /* "reset" */
%token LAST           /* "last" */
%token IF             /* "if" */
%token THEN           /* "then" */
%token ELSE           /* "else" */
%token DOT            /* "." */
%token ON             /* "on" */
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
%right prec_list
%left EVERY
%left AUTOMATON
%left INIT
%left UNTIL
%left UNLESS
%nonassoc THEN
%nonassoc ELSE
%left  BAR
%left COMMA
%left RPAREN
%right MINUSGREATER
%left OR BARBAR
%left AMPERSAND AMPERAMPER
%left INFIX0 EQUAL
%right INFIX1
%left INFIX2 PLUS SUBTRACTIVE MINUS
%left STAR INFIX3
%left ON
%left INFIX4
%right prec_uminus
%right FBY
%right PRE ATOMIC
%right PREFIX
%right DOT

%start implementation_file
%type <Parsetree.implementation list> implementation_file

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
  | dl = decl_list(X) x = X
      { x :: dl }
  | x = X 
      { [x] }
;

implementation:
  | LET ide = ide EQUAL seq = seq_expression
      { Eletdefl(ide, seq) }
  | LET a = is_atomic k = kind ide = ide LPAREN f_args = vardec_list RPAREN
        RETURNS  LPAREN f_res = vardec_list RPAREN eq = equation
      { Efundecl(ide, { f_kind = k; f_atomic = a;
			f_args = f_args; f_res = f_res; f_body = eq;
			f_loc = localise $startpos(a) $endpos(eq) }) }
;


%inline is_atomic:
  | ATOMIC { true }
  | { false }
;

%inline kind:
  |      { Efun }
  | FUN  { Efun }
  | NODE { Enode }
;

%inline equation_list:
  | l = list_of(AND, equation) { l }
;

%inline equation:
   eq = localized(equation_desc) { eq }
;

equation_desc:
  | AUTOMATON opt_bar a = automaton_handlers opt_end
    { EQautomaton(List.rev a) }
  | MATCH e = seq_expression WITH opt_bar
    m = match_handlers opt_end
    { EQmatch(e, List.rev m) }
  | IF e = seq_expression THEN eq1 = equation
    ELSE eq2 = equation opt_end
    { EQifthenelse(e, eq1, eq2) }
  | IF e = seq_expression THEN eq1 = equation
      { EQifthenelse(e, b1, no_eq $startpos $endpos) }
  | IF e = seq_expression ELSE eq2 = equation
      { EQifthenelse(e, no_eq $startpos $endpos, eq2) }
  | RESET eq = equation EVERY e = expression
    { EQreset(eq, e) }
  | LOCAL v_list = vardec_list DO eq = equation DONE
    { EQlocal(v_list, eq) }
  | p = pateq EQUAL e = seq_expression
    { EQeq(p, e) }
  | INIT i = ide EQUAL e = seq_expression
    { EQinit(i, e) }
  | eq_list = equation_list
    { EQand(eq_list) }
;

opt_end:
  | { () } %prec prec_no_end
  | END { () }
;
 

/* states of an automaton in an equation*/
automaton_handlers:
  | a = automaton_handler
      { [a] }
  | ahs = automaton_handlers BAR a = automaton_handler
      { a :: ahs }
;

automaton_handler:
  | sp = state_pat MINUSGREATER v_list_eq = vardec_with_eq DONE
    { make { s_state = sp; s_vars = fst v_list_eq; s_body = snd v_list_eq;
	     s_until = []; s_unless = [] }
            $startpos $endpos}
  | sp = state_pat MINUSGREATER v_list_eq = vardec_with_eq THEN
                                e = emission
    { let v_list_e, body_e, st_e = e in
      make { s_state = sp; s_vars = fst v_list; s_body = snd v_list_eq;
	     s_until =
               [{ e_cond = scond_true $endpos(v_list_eq) $startpos(e);
                  e_reset = true; e_vars = v_list_e;
		  e_body = body_e;
		  e_next_state = st_e }];
	   s_unless = [] }
      $startpos $endpos}
  | sp = state_pat MINUSGREATER v_list_eq = vardec_with_eq CONTINUE
                                e = emission
    { let v_list_e, body_e, st_e = e in
      make { s_state = sp; s_vars = fst v_list; s_body = snd v_list_eq;
	     s_until =
               [{ e_cond = scond_true $endpos(v_list_eq) $startpos(e);
                  e_reset = false; e_vars = v_list_e;
		  e_body = body_e;
		  e_next_state = st_e }];
	   s_unless = [] }
      $startpos $endpos}
  | sp = state_pat MINUSGREATER v_list_eq = vardec_with_eq
         UNTIL e_until = escape_list
    { make
	{ s_state = sp; s_vars = fst v_list_eq; s_body = snd v_list_eq;
	  s_until = List.rev e_until; s_unless = [] }
       $startpos $endpos }
  | sp = state_pat MINUSGREATER v_list_eq = vardec_with_eq
         UNLESS e_unless = escape_list
    { make
	{ s_state = sp; s_vars = fst v_list_eq; s_body = snd v_list_eq;
	  s_until = []; s_unless = List.rev e_unless }
      $startpos $endpos }
;

escape :
  | sc = scondpat THEN s = state
    { { e_cond = sc; e_reset = true; e_vars = [];
	e_body = no_eq $startpos $endpos;
	e_next_state = s } }
  | sc = scondpat CONTINUE s = state
    { { e_cond = sc; e_reset = false; e_vars = [];
	e_body = no_eq $startpos $endpos;
	e_next_state = s } }
  | sc = scondpat THEN e = emission
    { let e_vars, e_body, s = e in
      { e_cond = sc; e_reset = true;
	e_vars = e_vars; e_body = e_body; e_next_state = s } }
  | sc = scondpat CONTINUE e = emission
    { let e_vars, e_body, s = e in
      { e_cond = sc; e_reset = false;
	e_vars = e_vars; e_body = e_body; e_next_state = s } }
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
  | e = simple_expression
      { (e) }
;

/* Block */
vardec_with_eq:
  | DO eq = equation
    { [], eq }
  | LOCAL v_list = vardec_list DO eq = equation
    { v_list, eq }
;

emission:
  | v_list_eq = vardec_with_eq IN s = state
    { let v_list, eq = v_list_eq in v_list, eq, s }
  | s = state
    { [], no_eq $startpos $endpos, s }
;

%inline vardec_list:
  | l = list_of(COMMA, vardec)
    { l }
;

vardec:
  | ide = ide
    { { var_name = ide; var_default = Ewith_nothing;
	var_loc = localise $startpos $endpos } }
  | ide = ide INIT e = simple_expression
    { { var_name = ide; var_default = Ewith_init e;
	     var_loc = localise $startpos $endpos id; Init(e) } }
  | ide = ide DEFAULT e = simple_expression
    { { var_name = ide; var_default = Ewith_default e;
	     var_loc = localise $startpos $endpos id; Init(e) } }
;

opt_bar:
  | BAR             { () }
  | /*epsilon*/     { () }
;


/* Pattern matching */
match_handlers:
  | m = match_handler
      { [ m ] }
  | mh = match_handlers BAR m = match_handler
      { m :: mh }
;

match_handler:
  | p = pattern MINUSGREATER v = vardec_with_eq
      { { m_pat = p; m_vars = fst v; m_body = snd v } }
;

/* Patterns */
pattern:
  | c = constructor
      { make (constr_pat c p) $startpos $endpos }
;

/* Pattern in an equation */
pateq:
  | ide = ide
    { [ide] }
  | l = pateq_comma_list
    { l }
  | LPAREN p = pateq RPAREN
    { p }
;

pateq_comma_list:
  | p1 = pateq COMMA p2 = pateq
      { [p2; p1] }
  | pc = pateq_comma_list COMMA p = pateq
      { p :: pc }
;


/* Expressions */
seq_expression :
  | e = expression
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
  | LAST i = ide
      { Elast(i) }
  | a = atomic_constant
      { Econst a }
  | LPAREN RPAREN
      { Econst Evoid }
  | LPAREN e = expression_comma_list RPAREN
      { Etuple (List.rev e) }
  | LPAREN e = seq_expression RPAREN
      { e.desc }
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
  | e1 = expression FBY e2 = expression
      { Eop(Efby, [e1; e2]) }
  | f = ext_ident l = simple_expression_list
      {  app f (List.rev l) }
  | f = constructor e = simple_expression
      {  constr f e }
  | PRE e = expression
      { Eop(Eunarypre, [e]) }
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
  | LET eq = equation IN e = seq_expression
      { Elet(false, defs, e) }
  | LET REC eq = equation IN e = seq_expression
      { Elet(true, eq, e) }
;

constructor:
  | c = CONSTRUCTOR
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
  | b = BOOL
      { Ebool b }
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
