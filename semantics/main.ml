(* the main *)
open Misc
open Monad
open Opt
open Initial
open Coiteration
open Location
   
               
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
  
let eval_error () =
  Format.eprintf "Evaluation error.@.";
  raise Error

(* evaluate the main node [main] given by option [-s] for [n] steps *)
(* with check *)
let eval source_name main number check =
  let p = parse_implementation_file source_name in
  let p = Scoping.program p in
  let p = Write.program p in
  let* genv = Coiteration.program Initial.genv0 p in
  let* r =
    match main with
    | None -> return ()
    | Some(main) ->
         let* r =
           (* make [n] steps and checks that every step returns [true] *)
           if check then Coiteration.check genv main number
           else
             (* make [n] steps *)
             Coiteration.run genv main Format.std_formatter number in
         return r in
  return r

 let eval filename =
  if Filename.check_suffix filename ".zls"
  then
    Location.initialize filename;
    let r = eval filename !main_node !number_of_steps !set_check in
    match r with | None -> eval_error () | Some _ -> ()
                                                   
let doc_main = "\tThe main node to evaluate"
let doc_number_of_steps = "\tThe number of steps"
let doc_check = "\tCheck that the simulated node returns true"
let doc_verbose = "\tVerbose mode"
let doc_no_assert = "\tNo check of assertions"

let errmsg = "Options are:"

           
let main () =
  try
    Arg.parse (Arg.align
                 [ "-s", Arg.String set_main, doc_main;
                   "-n", Arg.Int set_number, doc_number_of_steps;
                   "-check", Arg.Set set_check, doc_check;
                   "-v", Arg.Set set_verbose, doc_verbose;
                   "-noassert", Arg.Set no_assert, doc_no_assert])
      eval
      errmsg
  with
  | Scoping.Error -> exit 2
  
let _ = main ()
let _ = exit 0
            
