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
open Zlocation
open Zparsetree

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
(*added here*)
%token ASSUME         /* "assume" */
(*added here*)
%token R_MOVE         /* "move_robot_zls" */
(*added here*)
%token R_CONTROL      /* "control_robot_zls" */
(*added here*)
%token R_STORE        /* "robot_store" */
(*added here*)
%token R_STR          /* "robot_str" */
(*added here*)
%token R_GET          /* "robot_get" */
(*added here*)
%token IP             /* "ip" */
(*added here*)
%token OP             /* "op" */
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
%token BOX            /* "box" */
%token DIAMOND        /* "diamond" */
%token MODELS         /* "models" */
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
%type <Zparsetree.implementation list> implementation_file

%start interface_file
%type <Zparsetree.interface list> interface_file

%start scalar_interface_file
%type <Zparsetree.interface list> scalar_interface_file

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
      { Printf.printf "implementation: type declaration: type %s = ...\n" id; 
      Etypedecl(id, tp, td) }

  | LET STATIC ide = ide EQUAL seq = seq_expression
      { Econstdecl(ide,                            
               { desc=Erefinement(
                    ("emptyalias", make (Etypeconstr(Name("emptytype"), [])) $startpos $endpos),
                    {desc=Econst(Ebool(true));loc=localise $startpos(ide) $endpos(ide)}
                );loc=localise $startpos(ide) $endpos(ide) },                                                        
            true, seq) }
            
    (* refinement variable decl *)
  /* | LET ide = ide COLON obj = ide LBRACE seq1 = seq_expression RBRACE EQUAL seq2 = seq_expression */
  | LET ide = ide COLON ty_refine = type_expression EQUAL seq2 = seq_expression
      { Printf.printf "Erefinementdecl\n";
          Econstdecl(ide, ty_refine, false, seq2) }
          
    (*added here, varable annotation using ip and op keywords*)
  | LET ide = ide LBRACE OP seq1= expression RBRACE EQUAL seq2= seq_expression
      { Eipopannotation (ide, seq1, seq2, true) }
  | LET ide = ide LBRACE IP seq1= expression RBRACE EQUAL seq2= seq_expression
      { Eipopannotation (ide, seq1, seq2, false) }    

    (* non-refinement variable decl *)
  | LET ide = ide EQUAL seq = seq_expression
  | LET ide = ide COLON ext_ident EQUAL seq = seq_expression
      { Printf.printf "Erefinementdecl\n";
          Econstdecl(ide,            
               { desc=Erefinement(
                    ("emptyalias", make (Etypeconstr(Name("emptytype"), [])) $startpos $endpos),
                    {desc=Econst(Ebool(true));loc=localise $startpos(ide) $endpos(ide)}
                );loc=localise $startpos(ide) $endpos(ide) },
               false, seq) }        

    (* basic refinement function *)
  /* | LET ide = ide fn = simple_pattern_list COLON obj = ide LBRACE seq1 = seq_expression RBRACE EQUAL seq2 = seq_expression */
  | LET ide = ide fn = simple_pattern_list COLON retrefine=type_expression EQUAL seq2=seq_expression
      { Printf.printf "Efundecl\n"; Efundecl(ide, { 
            f_kind = A; f_atomic = false;
            f_args = fn;
            f_body = seq2;
			f_loc = localise $startpos(fn) $endpos(seq2);
            f_retrefine = retrefine
             }) }

    (* non-refinement function*)
  | LET ide = ide fn = simple_pattern_list EQUAL seq = seq_expression    
  | LET ide = ide fn = simple_pattern_list COLON ide EQUAL seq = seq_expression
        { Printf.printf "Efundecl trivially true\n"; Efundecl(ide, { f_kind = A; f_atomic = false;
			f_args = fn; f_body = seq;
			f_loc = localise $startpos(fn) $endpos(seq);
            f_retrefine = {
                desc=Erefinement(
                    ("emptyalias", make (Etypeconstr(Name("emptytype"), [])) $startpos $endpos),
                    {desc=Econst(Ebool(true));loc=localise $startpos(ide) $endpos(ide)}
                );loc=localise $startpos(ide) $endpos(ide)
                }  } )
        }
  (* refinement function with WHERE *)
  | LET ide = ide fn = simple_pattern_list COLON retrefine=type_expression EQUAL
	seq = seq_expression WHERE r = is_rec eqs = equation_list
        { Printf.printf "refinement function with WHERE\n"; Efundecl(ide, { f_kind = A; f_atomic = false; 
            f_args = fn; f_body = make(Elet(r, eqs, seq)) $startpos(seq) $endpos(eqs);
		    f_loc = localise $startpos(fn) $endpos(eqs);
            f_retrefine = retrefine }) 
        }

  (* non-refinement function with WHERE *)
  | LET ide = ide fn = simple_pattern_list EQUAL seq = seq_expression WHERE r = is_rec eqs = equation_list
  | LET ide = ide fn = simple_pattern_list COLON ide EQUAL seq = seq_expression WHERE r = is_rec eqs = equation_list
        { Printf.printf "non-refinement function with WHERE\n"; Efundecl(ide, { f_kind = A; f_atomic = false; f_args = fn;
			f_body = make(Elet(r, eqs, seq))
				 $startpos(seq) $endpos(eqs);
		       f_loc = localise $startpos(fn) $endpos(eqs);
               f_retrefine={
                desc=Erefinement(
                    ("emptyalias", make (Etypeconstr(Name("emptytype"), [])) $startpos $endpos),
                    {desc=Econst(Ebool(true));loc=localise $startpos(ide) $endpos(ide)}
                );loc=localise $startpos(ide) $endpos(ide)
                } }) 
        }
  (* kinded refinement function *)
  | is_let a = is_atomic k = kind ide = ide fn = simple_pattern_list COLON retrefine=type_expression EQUAL seq2 = seq_expression
        { Printf.printf "Kinded refinement function\n"; 
            Efundecl(ide, { f_kind = k; f_atomic = a; f_args = fn; f_body = seq2;
                                    f_loc = localise $startpos(fn) $endpos(fn);
                                    f_retrefine = retrefine} )
        }
  (* kind refinement function with where*)
  | is_let a = is_atomic k = kind ide = ide fn = simple_pattern_list COLON retrefine=type_expression EQUAL 
    seq = seq_expression WHERE r = is_rec eqs = equation_list
      { Printf.printf "Kinded refinement function with WHERE\n"; 
        Efundecl(ide, { f_kind = k; f_atomic = a; f_args = fn; f_body = make(Elet(r, eqs, seq)) $startpos(seq) $endpos(eqs);
			                      f_loc = localise $startpos(fn) $endpos(eqs);
                                  f_retrefine = retrefine }) }

  /* BAD!: here if changed to Efundecl will cause error: Invalid_argument("List.map2") */
  /* which is in "dune build" stage */
  /* -> Now the verification is handled in Efundecl, see z3refinement.ml */
  (* kinded non-refinement function *)
  | is_let a = is_atomic k = kind ide = ide fn = simple_pattern_list EQUAL seq = seq_expression
        { Printf.printf "Kinded non-refinement function\n"; 
            Efundecl(ide,
            { f_kind = k; f_atomic = a; f_args = fn; f_body = seq;
            f_loc = localise $startpos(fn) $endpos(seq);
            f_retrefine = {
                desc=Erefinement(
                    ("emptyalias", make (Etypeconstr(Name("emptytype"), [])) $startpos $endpos),
                    {desc=Econst(Ebool(true));loc=localise $startpos(ide) $endpos(ide)}
                );loc=localise $startpos(ide) $endpos(ide)
                } 
            }) 
        }                                  
  (* kinded non-refinement function with WHERE *) 
  | is_let a = is_atomic k = kind ide = ide
	  fn = simple_pattern_list EQUAL seq = seq_expression
          WHERE r = is_rec eqs = equation_list
        { Printf.printf "Kinded non-refinement function with WHERE\n";
            Efundecl(ide, { f_kind = k; f_atomic = a; f_args = fn;
			f_body = make(Elet(r, eqs, seq))
				 $startpos(seq) $endpos(eqs);
			f_loc = localise $startpos(fn) $endpos(eqs);
            f_retrefine = {
                desc=Erefinement(
                    ("emptyalias", make (Etypeconstr(Name("emptytype"), [])) $startpos $endpos),
                    {desc=Econst(Ebool(true));loc=localise $startpos(ide) $endpos(ide)}
                );loc=localise $startpos(ide) $endpos(ide)
                } }) 
        }
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
      { Printf.printf "interface: type declaration\n";
          Einter_typedecl(i, tp, td) }
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
      { Printf.printf "scalar_interface: type declaration\n";
          [make (Einter_typedecl(i, tp, td)) $startpos $endpos] }
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
      { Printf.printf "type_declaration_desc: Eabstract_type\n";
          Eabstract_type }
  | EQUAL l = list_of(BAR, localized(constr_decl_desc))
      { Evariant_type (l) }
  | EQUAL BAR l = list_of(BAR, localized(constr_decl_desc))
      { Evariant_type (l) }
  | EQUAL LBRACE s = label_list(label_type) RBRACE
      { Printf.printf "type_declaration_desc: Erecord_type\n";
          Erecord_type (s) }
  | EQUAL LBRACE label_type = label_type BAR seq = seq_expression RBRACE
      { Printf.printf "type_declaration_desc: Ecustom_refinement_type\n";
          Ecustom_refinement_type (label_type, seq) }
  | EQUAL t = type_expression
      { Eabbrev(t) }
;

type_params:
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
  | i = IDENT COLON t = type_expression
  { Printf.printf "label_type: %s:type_expression\n" i;
      (i, t) }
  | LPAREN t=label_type RPAREN { t }
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
  | l = list_of(AND, equation) { Printf.printf "Equation List with %d elements\n" (List.length l); l }
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
  (*added here*)
  | R_STORE p = pattern EQUAL rob = robot_expression
    { EQeq(p, make (Estore(rob.cmd, rob.key)) $startpos(rob) $endpos(rob)) }
    (*added here*)
  | R_GET p = pattern EQUAL rob = rbt_expression
    { EQeq(p, make (Eget(rob.cm)) $startpos(rob) $endpos(rob)) }
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
  (*added here
  | R_STORE r = robot_expression 
     {EQstore(r)} *)  
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
automaton_handlers(X):
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

escape:
  | scondpat THEN state
      { { e_cond = $1; e_reset = true; e_block = None; e_next_state = $3 } }
  | scondpat CONTINUE state
      { { e_cond = $1; e_reset = false; e_block = None; e_next_state = $3 } }
  | scondpat THEN emission state
      { { e_cond = $1; e_reset = true; e_block = Some($3); e_next_state = $4 } }
  | scondpat CONTINUE emission state
      { { e_cond = $1; e_reset = false; e_block = Some($3); e_next_state = $4 } }
;

escape_list:
  | e = escape
      { [e] }
  | el = escape_list ELSE e = escape
      { e :: el }
;

state:
  | c = CONSTRUCTOR
      { make (Estate0(c)) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN e = expression RPAREN
      { make (Estate1(c, [e])) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN l = expression_comma_list RPAREN
      { make (Estate1(c, List.rev l)) $startpos $endpos }
;

state_pat:
  | c = CONSTRUCTOR
      { make (Estate0pat(c)) $startpos $endpos }
  | c = CONSTRUCTOR LPAREN l = list_of(COMMA, IDENT) RPAREN
      { make (Estate1pat(c, l)) $startpos $endpos }
;

/* Pattern on a signal */
scondpat:
  | sc = localized(scondpat_desc) { sc }
;

scondpat_desc :
  | e = simple_expression p = simple_pattern
      { Econdpat(e, p) }
  | e = simple_expression
      { Econdexp(e) }
  | UP e = simple_expression
      { Econdexp (make (Eop(Eup, [e])) $startpos $endpos) }
  (*added here*)
  | R_MOVE e = simple_expression
      { Econdexp (make (Eop(Emove, [e])) $startpos $endpos)}
  (*added here*)
  | R_CONTROL e = simple_expression
      { Econdexp (make (Eop(Econtrol, [e])) $startpos $endpos)}
  (*added here*)
  | R_STR e = simple_expression
      { Econdexp (make (Eop(Estr, [e])) $startpos $endpos)}
  (*added here*)
  (*| IP e= simple_expression
      { Econdexp (make (Eop(Einp, [e])) $startpos $endpos)}*)
  (*added here*)
  | OP e= simple_expression
      { Econdexp (make (Eop(Eoup, [e])) $startpos $endpos)}
  (*added here
  | R_STORE rob = robot_expression
       {Econdexp (make (Eop(Estore, [rob])) $startpos $endpos)}*)
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
    (*Add pattern for dependent type*)
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
      { Printf.printf "simple_pattern: ide\n";
          make (Evarpat i) $startpos $endpos }
  | LPAREN p = pattern RPAREN
      { p }
  | LPAREN p = pattern_comma_list RPAREN
      { Printf.printf "simple_pattern: LPAREN pattern_comma_list RPAREN\n";
          make (Etuplepat (List.rev p)) $startpos $endpos }
  | LPAREN RPAREN
      { make (Econstpat(Evoid)) $startpos $endpos }
  | UNDERSCORE
      { make Ewildpat $startpos $endpos }
  | LPAREN p = pattern COLON t = type_expression RPAREN
      { Printf.printf "simple_pattern: ( p:type_expression )\n";
          make (Etypeconstraintpat(p, t)) $startpos $endpos }
  | LBRACE p = pattern_label_list RBRACE
      { make (Erecordpat(p)) $startpos $endpos }
;

pattern_comma_list:
  | p1 = pattern COMMA p2 = pattern
      { [p2; p1] }
  | pc = pattern_comma_list COMMA p = pattern
      { p :: pc }
;

pattern_label_list:
  | p = pattern_label SEMI pl = pattern_label_list
      { p :: pl }
  | p = pattern_label
      { [p] }
  | UNDERSCORE
      { [] }
  | /*epsilon*/
      { [] }
;

pattern_label:
  | ei = ext_ident EQUAL p = pattern
      { (ei, p) }
;

/* Expressions */
seq_expression:
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
      { Printf.printf "Desc constr0\n"; Econstr0(c) }
  (* support for refinement types *)
  | name_var = ide COLON basetype = ide LBRACE seq1 = seq_expression RBRACE 
      { Printf.printf "Refinement tuple\n"; Erefinementtype(name_var, basetype, seq1) }
  | i = ext_ident
      { Printf.printf "Desc var\n"; Evar i }
  | LBRACKET RBRACKET
      { Printf.printf "Desc nil_desc\n"; nil_desc }
  | LBRACKET l = list_of(SEMI, expression) RBRACKET
      { Printf.printf "Desc cons_list_desc\n"; cons_list_desc l ($startpos($1)) ($endpos($3)) }
  | LAST i = ide
      { Printf.printf "Desc last\n"; Elast(i) }
  | a = atomic_constant
      { Printf.printf "Desc const\n"; Econst a }
  | LBRACE l = label_expression_list RBRACE
      { Printf.printf "Desc record\n"; Erecord(l) }
  | LBRACE e = simple_expression WITH l = label_expression_list RBRACE
      { Printf.printf "Desc record with\n"; Erecord_with(e, l) }
  | LPAREN RPAREN
      { Printf.printf "Desc void\n"; Econst Evoid }
  | LPAREN e = expression_comma_list RPAREN
      { Printf.printf "Desc Tuple\n"; Etuple (List.rev e) }

(*
  (* refinement tuples *)
  | LPAREN e = expression_comma_list RPAREN COLON tl = type_star_list BAR e_ref = seq_expression 
      { Printf.printf "Desc Refinement Tuple\n"; Erefinementtuple (List.rev e, make(Etypetuple(List.rev tl)) $startpos $endpos, e_ref) }
  (* refinement pair function argument*)
//   | LPAREN e = expression_comma_list COLON tl = type_star_list BAR e_ref = seq_expression RPAREN
//       { Printf.printf "Desc Refinement Pair\n"; Erefinementfunpair( List.rev e, make(Etypetuple(List.rev tl)) $startpos $endpos, e_ref) }
*)
  | LPAREN e = seq_expression RPAREN
      { Printf.printf "Desc seq expression\n"; e.desc }
  | LPAREN e = simple_expression COLON t = type_expression RPAREN
      { Printf.printf "Desc type constraint\n"; Etypeconstraint(e, t) }
  | e = simple_expression DOT i = ext_ident
      { Printf.printf "Desc record access\n"; Erecord_access(e, i) }
  | LBRACKETBAR e1 = simple_expression BAR e2 = simple_expression RBRACKETBAR
      { Printf.printf "Desc concat\n"; Eop(Econcat, [e1; e2]) }
  | LBRACKETBAR e1 = simple_expression WITH i = simple_expression
					     EQUAL e2 = expression RBRACKETBAR
      { Printf.printf "Desc update\n"; Eop(Eupdate, [e1; i; e2]) }
;

simple_expression_list:
  | e = simple_expression
	  { [e] }
  | l = simple_expression_list e = simple_expression
	  { e :: l }
  ;

expression_comma_list:
  | ecl = expression_comma_list COMMA e = expression
      { e :: ecl }
  | e1 = expression COMMA e2 = expression
      { [e2; e1] }
;

(* refinement tuple definition *)
// refinement_expression_comma_list:
//   | ecl = refinement_expression_comma_list COMMA e = expression
//       { e :: ecl}
//   | e1 = expression COLON obj = ide LBRACE seq1 = seq_expression RBRACE COMMA e2 = expression COLON obj = ide LBRACE seq1 = seq_expression RBRACE
//       { [Erefinement(); Erefinement()] }
// ;

expression:
  | x = localized(expression_desc)
    { x }
;

expression_desc:
  | e = simple_expression_desc
      { Printf.printf "Simple expression\n"; e }
  | e = expression_comma_list %prec prec_list
      { Printf.printf "Tuple\n"; Etuple(List.rev e) }
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
  (* support for refinement types *)
  | name_var = ide COLON basetype = ide LBRACE seq1 = seq_expression RBRACE 
      { Printf.printf "Refinement tuple\n"; Erefinementtype(name_var, basetype, seq1) }
  (*added here*)
  | R_MOVE e = expression
      { Eop(Emove, [e])}
  (*added here*)
  | R_CONTROL LPAREN e1= expression COMMA e2=expression RPAREN
      { Eop(Econtrol, [e1;e2])}
  (*added here*)
  | R_STR LPAREN e1= expression COMMA e2=expression RPAREN
      { Eop(Estr, [e1;e2])}
  (*added here*)    
  | e1= expression LBRACE IP QUOTE e2=expression QUOTE RBRACE
      { Eop(Einp, [e1;e2])}
  (*added here*)    
  | OP e=expression 
      { Eop(Eoup, [e])}

  | e1 = expression MODELS e2 = expression
    { Eop(Emodels, [e1; e2])}
  (*added here
  | R_STORE rob = robot_expression
      { Eop(Estore, [rob])}*)
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

  |  { Printf.printf "expression_desc: Econst(Ebool(true))\n"; Econst(Ebool(true))}
  /* | empty { Printf.printf "expression_desc: void\n"; Econst(Evoid)} */


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
      { Printf.printf "expression: INFIX0: e1 %s e2\n" i;
          binop i e1 e2 ($startpos(i)) ($endpos(i)) }
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
      { Printf.printf "expression_desc: e1 && e2\n";
          binop "&&" e1 e2 ($startpos($2)) ($endpos($2)) }
  | e1 = expression BARBAR e2 = expression
      { binop "||" e1 e2 ($startpos($2)) ($endpos($2)) }
  | p = PREFIX e = expression
      { Printf.printf "expression_desc: PREFIX: %s e\n" p;
          unop p e ($startpos(p)) ($endpos(p)) }

    (* add box and diamond *)
  /* | b = BOX LPAREN e = expression RPAREN
      { Printf.printf "expression_desc: box(e)\n"; 
        unop "box" e ($startpos(b)) ($endpos(b)) }
  | d = DIAMOND LPAREN e = expression RPAREN
      { Printf.printf "expression_desc: diamond(e)\n"; 
        unop "diamond" e ($startpos(d)) ($endpos(d)) } */

  | ltl_operator = ltl_operator LPAREN e = expression RPAREN
      { Printf.printf "expression_desc: ltl_operator: %s(e)\n" ltl_operator; 
        unop ltl_operator e ($startpos(ltl_operator)) ($endpos(ltl_operator)) }     

  | e = simple_expression
          LBRACE s1 = size_expression DOTDOT s2 = size_expression RBRACE
      { Eop(Eslice(s1, s2), [e]) }
  | e1 = simple_expression DOT LPAREN e2 = expression RPAREN
      { Eop(Eaccess, [e1; e2]) }
  | LET defs = equation_list IN e = seq_expression
      { Printf.printf "Let with list of equations\n"; Elet(false, defs, e) }
  | LET REC defs = equation_list IN e = seq_expression
      { Printf.printf "Let Rec with list of equations\n"; Elet(true, defs, e) }
  | PERIOD p = period_expression
      { Eperiod(p) }
  (*added here*)
  | ASSUME e = expression 
  	{Eassume(e)}
  (*added here
  | R_MOVE e = expression
        {Emove(e)}*)
  (*added here*)
  | R_STORE rob = robot_expression
        {Estore(rob.cmd, rob.key)}
  (*added here*)
  | R_GET rob = rbt_expression
        {Eget(rob.cm)}
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

%inline ltl_operator:
    | BOX { "box" }
    | DIAMOND { "diamond" }

/* Periods */
period_expression:
  | LPAREN per = expression RPAREN /* period */
      { { p_phase = None; p_period = per } }
  | LPAREN ph = expression BAR per = expression RPAREN /* period */
      { { p_phase = Some(ph); p_period = per } }
;
(*added here*)
robot_expression:
  | LPAREN r_cmd = STRING COMMA r_key = FLOAT RPAREN
      {{cmd = r_cmd; key = r_key}}
  (*added here*)
rbt_expression:
  | LPAREN r_cm = STRING   RPAREN
      {{cm = r_cm}}  
(*added here
ip_op_expression:
  | OP chan= expression
      {{channel= chan}}
;*)      
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
      { Printf.printf "ide: IDENT: %s\n" i;
          i }
  | LPAREN i = infx RPAREN
      { i }
;

ext_ident:
  | q = qual_ident
      { Printf.printf "ext_ident: qual_ident\n";
          Modname(q) }
  | i = ide
      { Printf.printf "ext_ident: ide: %s\n" i;
          Name(i) }
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
      { Zparsetree.A }
  | AFUN
      { Zparsetree.A }
  | ADFUN
      { Zparsetree.AD }
  | DFUN
      { Zparsetree.D }
  | CFUN
      { Zparsetree.C }
  | SFUN
      { Zparsetree.S }
  | ASFUN
      { Zparsetree.AS }
  | PFUN
      { Zparsetree.P }
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
      { Printf.printf "type star list\n"; make(Etypetuple(List.rev tl)) $startpos $endpos}
  (* functions with refinement pairs *)
  | tl = type_star_list BAR e = seq_expression
      { Printf.printf " function with refinement pair\n"; make(Erefinementpairfuntype(List.rev tl, e)) $startpos $endpos}
  | t_arg = type_expression a = arrow t_res = type_expression
      { Printf.printf "type exp -> type exp\n"; make(Etypefun(a, None, t_arg, t_res)) $startpos $endpos}
  | LPAREN id = IDENT COLON t_arg = type_expression RPAREN
			    a = arrow t_res = type_expression
    { make(Etypefun(a, Some(id), t_arg, t_res)) $startpos $endpos}
  (*added here
  | LBRACE seq = seq_expression RBRACE {make(Eipoptype(seq)) $startpos $endpos}*)
  | LPAREN id = IDENT COLON t_arg = type_expression RPAREN
			    a = arrow t_res = type_expression
      { Printf.printf "type arrow and :\n"; make(Etypefun(a, Some(id), t_arg, t_res)) $startpos $endpos}
  (*Refinement type expression*)
  (* TODO: Make a refinement type data structure that stores all the data from this *)
  (*make(Erefinement(basetype, seq)) $startpos $endpos*)

  (* New-syntax Erefinement in type_expression *)
  | LBRACE label_type = label_type BAR seq = seq_expression RBRACE
    { Printf.printf "new-syntax type refinement\n"; make(Erefinement(label_type, seq)) $startpos $endpos}

  | LBRACE label_type_star_list = label_type_star_list BAR seq = seq_expression RBRACE
    {Printf.printf "new-syntax refinement tuple\n"; make(Erefinementlabeledtuple(List.rev label_type_star_list, seq)) $startpos $endpos}

  /* | basetype = simple_type LBRACE seq = seq_expression RBRACE 
      {Printf.printf "type refinement\n"; make(Erefinement(basetype, seq)) $startpos $endpos}  */

  | LPAREN id = IDENT COLON t_arg = simple_type LBRACE seq = seq_expression RBRACE RPAREN a = arrow t_res = type_expression
      { Printf.printf "type typefunrefinement\n"; make(Etypefunrefinement(a, Some(id), t_arg, t_res , seq)) $startpos $endpos}
;

simple_type:
  | t = type_var
      { Printf.printf "type var\n"; make (Etypevar t) $startpos $endpos }
  | i = ext_ident
      { Printf.printf "type constr\n"; make (Etypeconstr(i, [])) $startpos $endpos }
  | t = simple_type i = ext_ident
      { Printf.printf "simple type constr\n"; make (Etypeconstr(i, [t])) $startpos $endpos }
  (*simple refinement type*)

  /* | basetype = simple_type LBRACE seq = seq_expression RBRACE 
      { Printf.printf "type refinement simple type\n"; make(Erefinement(basetype, seq)) $startpos $endpos} */
   
  (* refinement type specification for pairs *)
  (*| binding_var = ide COLON basetype = simple_type
      { Printf.printf "type refinement pair\n"; make(Erefinementpair(binding_var, basetype)) $startpos $endpos}*)
  (*| LPAREN t = type_expression COMMA tl = type_comma_list RPAREN i = ext_ident
      { Printf.printf "type expression list\n"; make (Etypeconstr(i, t :: tl)) $startpos $endpos }*)
  | t_arg = simple_type LBRACKET s = size_expression RBRACKET
      { Printf.printf "type vec\n"; make(Etypevec(t_arg, s)) $startpos $endpos}
  | LPAREN t = type_expression RPAREN
      { Printf.printf "type expression\n"; t }
;

type_star_list:
  | t1 = simple_type STAR t2 = simple_type
      { [t2; t1] }
  | tsl = type_star_list STAR t = simple_type
      { t :: tsl }
;

label_type_star_list:
  | t1=label_type STAR t2 = label_type
      { Printf.printf "label_type star list\n";[t2; t1]}
  | tsl = label_type_star_list STAR t = label_type
      { t :: tsl }

type_var:
  | QUOTE i = IDENT
      { i }
;

type_comma_list:
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
