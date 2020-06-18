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

(* lexer.mll *)

{
open Lexing
open Parser
open Location

type lexical_error =
    Illegal_character
  | Unterminated_comment
  | Bad_char_constant
  | Unterminated_string;;

exception Lexical_error of lexical_error * location

let comment_depth = ref 0

let keyword_table = ((Hashtbl.create 149) : (string, token) Hashtbl.t);;

List.iter (fun (str,tok) -> Hashtbl.add keyword_table str tok) [
  "as", AS;
  "forall", FORALL;
  "automaton", AUTOMATON;
  "atomic", ATOMIC;
  "inline", INLINE;
  "continue", CONTINUE;
  "disc", DISC;
  "do", DO;
  "done", DONE;
  "until", UNTIL;
  "unless", UNLESS;
  "emit", EMIT;
  "present", PRESENT;
  "match", MATCH;
  "period", PERIOD;
  "with", WITH;
  "end", END;
  "exception", EXCEPTION;
  "external", EXTERNAL;
  "static", STATIC;
  "fun", FUN;
  "node", NODE;
  "hybrid", HYBRID;
  "discrete", DISCRETE;
  "proba", PROBA;
  "init", INIT;
  "initialize", INITIALIZE;
  "default", DEFAULT;
  "in", IN;
  "before", BEFORE;
  "out", OUT;
  "and", AND;
  "open", OPEN;
  "val", VAL;
  "local", LOCAL;
  "let", LET;
  "rec", REC;
  "where", WHERE;
  "open", OPEN;
  "fby", FBY;
  "next", NEXT;
  "up", UP;
  "der", DER;
  "reset", RESET;
  "pre", PRE;
  "type", TYPE;
  "every", EVERY;
  "true", BOOL(true); 
  "false", BOOL(false); 
  "or", OR;
  "of", OF;
  "on", ON;
  "last", LAST;
  "run", RUN;
  "if", IF;
  "then", THEN;
  "else", ELSE;
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

(*
let incr_linenum lexbuf =
  let pos = lexbuf.Lexing.lex_curr_p in
    lexbuf.Lexing.lex_curr_p <- { pos with
      Lexing.pos_lnum = pos.Lexing.pos_lnum + 1;
      Lexing.pos_bol = pos.Lexing.pos_cnum;
    }
*)

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
  | "("  { LPAREN }
  | ")"  { RPAREN }
  | "["  { LBRACKET }
  | "]"  { RBRACKET }
  | "[|" { LBRACKETBAR }
  | "|]" { RBRACKETBAR }
  | "*"  { STAR }
  | "{"  { LBRACE }
  | "}"  { RBRACE }
  | ":"  { COLON }
  | "::"  { COLONCOLON }
  | "="  { EQUAL }
  | "==" { EQUALEQUAL }
  | "+=" { PLUSEQUAL }
  | "&"  { AMPERSAND }
  | "'"  { QUOTE }
  | "&&" { AMPERAMPER }
  | "||" { BARBAR }
  | ","  { COMMA }
  | ";"  { SEMI }
  | ";;" { SEMISEMI }
  | "->" { MINUSGREATER }
  | "-A->" { AFUN }
  | "-D->" { DFUN }
  | "-AD->" { ADFUN }
  | "-AS->" { ASFUN }
  | "-C->" { CFUN }
  | "-S->" { SFUN }
  | "~D~>" { PFUN }
  | "|"  { BAR }
  | "-"  { MINUS }
  | "+"  { PLUS }
  | "-." { SUBTRACTIVE "-." }
  | "_"  { UNDERSCORE }
  | "?"  { TEST }
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
