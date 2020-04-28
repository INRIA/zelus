
(* The type of tokens. *)

type token = 
  | WITH
  | UNTIL
  | UNLESS
  | THEN
  | SUBTRACTIVE of (string)
  | STRING of (string)
  | STAR
  | RPAREN
  | RETURNS
  | RESET
  | REC
  | PREFIX of (string)
  | PRE
  | PLUS
  | OR
  | ON
  | NODE
  | MINUSGREATER
  | MINUS
  | MATCH
  | LPAREN
  | LOCAL
  | LET
  | LAST
  | INT of (int)
  | INIT
  | INFIX4 of (string)
  | INFIX3 of (string)
  | INFIX2 of (string)
  | INFIX1 of (string)
  | INFIX0 of (string)
  | IN
  | IF
  | IDENT of (string)
  | FUN
  | FLOAT of (float)
  | FBY
  | EVERY
  | EQUALEQUAL
  | EQUAL
  | EOF
  | END
  | ELSE
  | DOT
  | DONE
  | DO
  | DEFAULT
  | CONTINUE
  | CONSTRUCTOR of (string)
  | COMMA
  | BOOL of (bool)
  | BARBAR
  | BAR
  | AUTOMATON
  | ATOMIC
  | AND
  | AMPERSAND
  | AMPERAMPER

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val implementation_file: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Parsetree.implementation list)

module MenhirInterpreter : sig
  
  (* The incremental API. *)
  
  include MenhirLib.IncrementalEngine.INCREMENTAL_ENGINE
    with type token = token
  
end

(* The entry point(s) to the incremental API. *)

module Incremental : sig
  
  val implementation_file: Lexing.position -> (Parsetree.implementation list) MenhirInterpreter.checkpoint
  
end
