
(* The type of tokens. *)

type token = 
  | WITH
  | WHERE
  | VAL
  | UP
  | UNTIL
  | UNLESS
  | UNDERSCORE
  | TYPE
  | THEN
  | TEST
  | SUBTRACTIVE of (string)
  | STRING of (string)
  | STATIC
  | STAR
  | SFUN
  | SEMISEMI
  | SEMI
  | RUN
  | RPAREN
  | RESET
  | REC
  | RBRACKETBAR
  | RBRACKET
  | RBRACE
  | QUOTE
  | PROBA
  | PRESENT
  | PREFIX of (string)
  | PRE
  | PLUSEQUAL
  | PLUS
  | PFUN
  | PERIOD
  | OUT
  | OR
  | OPEN
  | ON
  | OF
  | NODE
  | NEXT
  | MINUSGREATER
  | MINUS
  | MATCH
  | LPAREN
  | LOCAL
  | LET
  | LBRACKETBAR
  | LBRACKET
  | LBRACE
  | LAST
  | INT of (int)
  | INLINE
  | INITIALIZE
  | INIT
  | INFIX4 of (string)
  | INFIX3 of (string)
  | INFIX2 of (string)
  | INFIX1 of (string)
  | INFIX0 of (string)
  | IN
  | IF
  | IDENT of (string)
  | HYBRID
  | FUN
  | FORALL
  | FLOAT of (float)
  | FBY
  | EXTERNAL
  | EXCEPTION
  | EVERY
  | EQUALEQUAL
  | EQUAL
  | EOF
  | END
  | EMIT
  | ELSE
  | DOTDOT
  | DOT
  | DONE
  | DO
  | DISCRETE
  | DISC
  | DFUN
  | DER
  | DEFAULT
  | CONTINUE
  | CONSTRUCTOR of (string)
  | COMMA
  | COLONCOLON
  | COLON
  | CHAR of (char)
  | CFUN
  | BOOL of (bool)
  | BEFORE
  | BARBAR
  | BAR
  | AUTOMATON
  | ATOMIC
  | ASFUN
  | AS
  | AND
  | AMPERSAND
  | AMPERAMPER
  | AFUN
  | ADFUN

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val scalar_interface_file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Parsetree.interface list)

val interface_file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Parsetree.interface list)

val implementation_file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Parsetree.implementation list)
