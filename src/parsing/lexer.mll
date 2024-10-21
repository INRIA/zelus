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

(* lexer.mll *)

{
open Lexing
open Parser
open Location

type lexical_error =
    Illegal_character
  | Unterminated_comment
  | Bad_char_constant
  | Unterminated_string

exception Lexical_error of lexical_error * Location.t

let comment_depth = ref 0

let keyword_table = ((Hashtbl.create 149) : (string, token) Hashtbl.t);;

List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok) [
  "and", AND;
  "assert", ASSERT;
  "atomic", ATOMIC;
  "automaton", AUTOMATON;
  "by", BY;
  "clock", CLOCK;
  "continue", CONTINUE;
  "const", CONST;
  "default", DEFAULT;
  "der", DER;
  "do", DO;
  "done", DONE;
  "downto", DOWNTO;
  "else", ELSE;
  "emit", EMIT;
  "end", END;
  "every", EVERY;
  "exception", EXCEPTION;
  "external", EXTERNAL;
  "false", BOOL(false); 
  "fby", FBY;
  "foreach", FOREACH;
  "forward", FORWARD;
  "fun", FUN;
  "hybrid", HYBRID;
  "if", IF;
  "in", IN;
  "init", INIT;
  "inline", INLINE;
  "last", LAST;
  "let", LET;
  "local", LOCAL;
  "match", MATCH;
  "node", NODE;
  "of", OF;
  "on", ON;
  "open", OPEN;
  "or", OR;
  "out", OUT;
  "period", PERIOD;
  "horizon", HORIZON;
  "pre", PRE;
  "present", PRESENT;
  "rec", REC;
  "reset", RESET;
  "resume", RESUME;
  "returns", RETURNS;
  "run", RUN;
  "then", THEN;
  "to", TO;
  "true", BOOL(true); 
  "type", TYPE;
  "static", STATIC;
  "unless", UNLESS;
  "until", UNTIL;
  "up", UP;
  "val", VAL;
  "where", WHERE;
  "while", WHILE;
  "with", WITH;
  "quo", INFIX3("quo");
  "mod", INFIX3("mod");
  "land", INFIX3("land");
  "lor", INFIX2("lor");
  "lxor", INFIX2("lxor");
  "lsl", INFIX4("lsl");
  "lsr", INFIX4("lsr");
  "asr", INFIX4("asr")
]


(* To buffer string literals *)

let initial_string_buffer = Bytes.create 256
let string_buff = ref initial_string_buffer
let string_index = ref 0

let reset_string_buffer () =
  string_buff := initial_string_buffer;
  string_index := 0;
  ()

let store_string_char c =
  if !string_index >= Bytes.length (!string_buff) then begin
    let new_buff = Bytes.create (Bytes.length (!string_buff) * 2) in
      Bytes.blit (!string_buff) 0 new_buff 0 (Bytes.length (!string_buff));
      string_buff := new_buff
  end;
  Bytes.set (!string_buff) (!string_index) c;
  incr string_index


let get_stored_string () =
  let s = Bytes.sub (!string_buff) 0 (!string_index) in
    string_buff := initial_string_buffer;
    s

let char_for_backslash = function
  | 'n' -> '\010'
  | 'r' -> '\013'
  | 'b' -> '\008'
  | 't' -> '\009'
  | c   -> c

let char_for_decimal_code lexbuf i =
  let c = 
    100 * (int_of_char(Lexing.lexeme_char lexbuf i) - 48) +
     10 * (int_of_char(Lexing.lexeme_char lexbuf (i+1)) - 48) +
          (int_of_char(Lexing.lexeme_char lexbuf (i+2)) - 48) in
  char_of_int(c land 0xFF)


}

rule main = parse 
  | [' ' '\010' '\013' '\009' '\012'] +   { main lexbuf }
  | "."  { DOT }
  | ".."  { DOTDOT }
  | ".T" { TRANSPOSE }
  | ".R" { REVERSE }
  | ".F" { FLATTEN }
  | "("  { LPAREN }
  | ")"  { RPAREN }
  | "["  { LBRACKET }
  | "]"  { RBRACKET }
  | "[|" { LBRACKETBAR }
  | "|]" { RBRACKETBAR }
  | "{"  { LBRACE }
  | "}"  { RBRACE }
  | "*"  { STAR }
  | ":"  { COLON }
  | "="  { EQUAL }
  | "==" { EQUALEQUAL }
  | "&"  { AMPERSAND }
  | "&&" { AMPERAMPER }
  | "'"  { QUOTE }
  | "||" { BARBAR }
  | ","  { COMMA }
  | ";"  { SEMI }
  | "->" { MINUSGREATER }
  | "-V->" { VFUN }
  | "-S->" { SFUN }
  | "-A->" { AFUN }
  | "-D->" { DFUN }
  | "-C->" { CFUN }
  | "<-" { LESSMINUS }
  | "|"  { BAR }
  | "/"  { DIV }
  | "-"  { MINUS }
  | "+"  { PLUS }
  | "++" { PLUSPLUS }
  | "-." { SUBTRACTIVE "-." }
  | "_"  { UNDERSCORE }
  | "?"  { TEST }
  | ">"  { GREATER }
  | "<"  { LESSER }
  | "<<"  { LLESSER }
  | ">>"  { GGREATER }
  | "last*" { LAST_STAR }
  | (['A'-'Z']('_' ? ['A'-'Z' 'a'-'z' ''' '0'-'9']) * as id) 
      {CONSTRUCTOR id}
  | (['A'-'Z' 'a'-'z'](['_' 'A'-'Z' 'a'-'z' ''' '0'-'9']) * as id) 
      { let s = Lexing.lexeme lexbuf in
          try
            Hashtbl.find keyword_table s
          with Not_found ->
            IDENT id }
  | ['0'-'9']+
  | '0' ['x' 'X'] ['0'-'9' 'A'-'F' 'a'-'f']+
  | '0' ['o' 'O'] ['0'-'7']+
  | '0' ['b' 'B'] ['0'-'1']+
      { INT (int_of_string(Lexing.lexeme lexbuf)) }
  | ['0'-'9']+ ('.' ['0'-'9']*)? (['e' 'E'] ['+' '-']? ['0'-'9']+)?
      { FLOAT (float_of_string(Lexing.lexeme lexbuf)) }
  | "\""
      { reset_string_buffer();
        let string_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        begin try
          string lexbuf
        with Lexical_error(Unterminated_string, Loc(_, string_end)) ->
          raise(Lexical_error(Unterminated_string, 
                             Loc(string_start, string_end)))
        end;
        lexbuf.lex_start_pos <- string_start - lexbuf.lex_abs_pos;
        STRING (Bytes.to_string(get_stored_string())) }
  | "'" [^ '\\' '\''] "'"
      { CHAR(Lexing.lexeme_char lexbuf 1) }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { CHAR(char_for_backslash (Lexing.lexeme_char lexbuf 2)) }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { CHAR(char_for_decimal_code lexbuf 2) }
  | "(*"
      { let comment_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        comment_depth := 1;
        begin try
          comment lexbuf
        with Lexical_error(Unterminated_comment, Loc(_, comment_end)) ->
          raise(Lexical_error(Unterminated_comment,
                              Loc(comment_start, comment_end)))
        end;
        main lexbuf }
   | ['!' '?' '~']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' 
          '<' '=' '>' '?' '@' '^' '|' '~'] *
      { PREFIX(Lexing.lexeme lexbuf) }
  | ['=' '<' '>' '&'  '|' '&' '$']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' 
          '?' '@' '^' '|' '~'] *
      { INFIX0(Lexing.lexeme lexbuf) }
  | ['@' '^']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' 
          '?' '@' '^' '|' '~'] *
      { INFIX1(Lexing.lexeme lexbuf) }
  | ['+' '-']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' 
          '?' '@' '^' '|' '~'] *
      { INFIX2(Lexing.lexeme lexbuf) }
  | "**"
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' 
          '?' '@' '^' '|' '~'] *
      { INFIX4(Lexing.lexeme lexbuf) }
  | ['*' '/' '%']
      ['!' '$' '%' '&' '*' '+' '-' '.' '/' ':' '<' '=' '>' 
          '?' '@' '^' '|' '~'] *
      { INFIX3(Lexing.lexeme lexbuf) }
  | eof            {EOF}
  | _              {raise (Lexical_error (Illegal_character,
                                          Loc(Lexing.lexeme_start lexbuf, 
                                             Lexing.lexeme_end lexbuf)))}
      
and comment = parse
    "(*"
      { comment_depth := succ !comment_depth; comment lexbuf }
  | "*)"
      { comment_depth := pred !comment_depth;
        if !comment_depth > 0 then comment lexbuf }
  | "\""
      { reset_string_buffer();
        let string_start = lexbuf.lex_start_pos + lexbuf.lex_abs_pos in
        begin try
          string lexbuf
        with Lexical_error(Unterminated_string, Loc(_, string_end)) ->
          raise(Lexical_error(Unterminated_string, 
                             Loc(string_start, string_end)))
        end;
        comment lexbuf }
  | "''"
      { comment lexbuf }
  | "'" [^ '\\' '\''] "'"
      { comment lexbuf }
  | "'" '\\' ['\\' '\'' 'n' 't' 'b' 'r'] "'"
      { comment lexbuf }
  | "'" '\\' ['0'-'9'] ['0'-'9'] ['0'-'9'] "'"
      { comment lexbuf }
  | eof
      { raise(Lexical_error(Unterminated_comment,
                           Loc(0,Lexing.lexeme_start lexbuf))) }
  | _
      { comment lexbuf }

and string = parse
    '"' 
      { () }
  | '\\' ("\010" | "\013" | "\013\010") [' ' '\009'] *
      { string lexbuf }
  | '\\' ['\\' '"'  'n' 't' 'b' 'r']
      { store_string_char(char_for_backslash(Lexing.lexeme_char lexbuf 1));
        string lexbuf }
  | '\\' ['0'-'9'] ['0'-'9'] ['0'-'9']
      { store_string_char(char_for_decimal_code lexbuf 1);
         string lexbuf }
  | eof
      { raise (Lexical_error
                (Unterminated_string, Loc(0, Lexing.lexeme_start lexbuf))) }
  | _
      { store_string_char(Lexing.lexeme_char lexbuf 0);
        string lexbuf }

(* eof *)
