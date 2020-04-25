(* the main *)
open Initial
open Coiteration
open Location
   
exception Error
        
let lexical_error err loc =
  Format.eprintf "%aIllegal character.@." output_location loc;
  raise Error

let syntax_error loc =
  Format.eprintf "%aSyntax error.@." output_location loc;
  raise Error

let parse parsing_fun lexing_fun source_name =
  let ic = open_in source_name in
  let lexbuf = Lexing.from_channel ic in
  lexbuf.Lexing.lex_curr_p <-
    { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = source_name };
  try
    parsing_fun lexing_fun lexbuf
  with
  | Lexer.Lexical_error(err, loc) ->
     close_in ic; lexical_error err loc
  | Parser.Error ->
     close_in ic;
     syntax_error
       (Loc(Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf))
     
let parse_implementation_file source_name =
  parse Parser.implementation_file Lexer.main source_name
  
let eval modname filename =
  let program = parse_implementation_file source_name in
  Coiteration.eval program

let eval file =
  if Filename.check_suffix file ".zls" || Filename.check_suffix file ".zlus"
  then
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    eval modname filename
  else
    None

let doc_main "The main node to evaluate\n"

let errmsg = "Options are:"

let main () =
  Arg.parse (Arg.align
      [
        "-main", Arg.String set_main, doc_main
      ])
      eval
      errmsg

let _ = main ()
let _ = exit 0
