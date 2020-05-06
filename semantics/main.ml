(* the main *)
open Monad
open Opt
open Initial
open Coiteration
open Location
   
exception Error
        
let main_node = ref None
let set_main s = main_node := Some(s)

let number_of_steps = ref 0
let set_number n = number_of_steps := n
                 
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

(* evaluate the main node [m] given by option [-s] for [n] steps *)
let eval source_name m n =
  let info_ff = Format.formatter_of_out_channel stdout in
  (* Format.pp_set_max_boxes info_ff max_int; *)
  let p = parse_implementation_file source_name in
  let p = Scoping.program p in
  let p = Write.program p in
  let* genv = Coiteration.program Initial.genv0 p in
  let* m = m in
  let* r =
    Coiteration.main genv m (Initial.Output.value_list_and_flush info_ff) n in
  return r

 let eval filename =
  if Filename.check_suffix filename ".zls" || Filename.check_suffix filename ".zlus"
  then
    (* let modname = 
      String.capitalize_ascii
        (Filename.basename (Filename.chop_extension filename)) in *)
    Location.initialize filename;
    let r = eval filename !main_node !number_of_steps in
    match r with | None -> eval_error () | Some _ -> ()
                                                   
let doc_main = "The main node to evaluate\n"
let doc_number_of_steps = "The number of steps\n"

let errmsg = "Options are:"

           
let main () =
  try
    Arg.parse (Arg.align
                 [ "-s", Arg.String set_main, doc_main;
                   "-n", Arg.Int set_number, doc_number_of_steps ])
      eval
      errmsg
  with
  | Scoping.Error | Error -> exit 2
  
let _ = main ()
let _ = exit 0
            
