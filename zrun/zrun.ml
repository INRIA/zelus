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

(* the main *)
open Misc
open Monad
open Opt
open Value
open Lident
open Primitives
open Coiteration
open Location
               
let lexical_error err loc =
  Format.eprintf "%aIllegal character.@." output_location loc;
  raise Stdlib.Exit

let syntax_error loc =
  Format.eprintf "%aSyntax error.@." output_location loc;
  raise Stdlib.Exit

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

  
(* check that a value is causally correct (non bot) *)
(* and initialized (non nil) *)
let not_bot_nil v =
  let not_bot_nil v =
    match v with
    | Vbot ->
       Format.eprintf "Causality error.@."; raise Stdlib.Exit
    | Vnil ->
       Format.eprintf "Initialization error.@."; raise Stdlib.Exit
    | Value(v) ->
       return v in
  not_bot_nil v
    
(* run a combinatorial expression *)
(* returns the number of successful iterations *)
let run_fun output fv n =
  let rec runrec i =
    if i = n then i
    else
      let v = Result.to_option (fv Vvoid) in
      match v with
      | None -> i
      | Some(v) ->
         let _ = output v in
         runrec (i+1) in
  runrec 0
      
(* run a stream process *)
let run_node output init step n =
  let rec runrec s i =
    if i = n then i
    else
      let v = Result.to_option (step s (Value(Vvoid))) in
      match v with
      | None -> i
      | Some(v, s) ->
         let v = not_bot_nil v in
         match v with
         | None -> i
         | Some(v) ->
            let _ = output v in
            runrec s (i+1) in
  runrec init 0

(* The main entry function *)
let run genv main ff n =
  let* fv = find_gvalue_opt (Name main) genv in
  (* the main function must be of type : unit -> t *)
  (* the main function must be of type : unit -> t *)
  match fv with
  | Vfun(fv) ->
     let i = run_fun (Output.pvalue_and_flush ff) fv n in
     if i < n then Format.printf "Run failed: only %i iterations.\n" i;
     return ()
  | Vnode { init; step } ->
     let i = run_node (Output.pvalue_and_flush ff) init step n in
     if i < n then Format.printf "Run failed: only %i iterations.\n" i;
     return ()
  | _ -> None
     
  
let check genv main n =
  let* fv = find_gvalue_opt (Name main) genv in
  (* the main function must be of type : unit -> bool *)
  let output v =
    if v = Vbool(true) then return () else None in
  match fv with
  | Vfun(fv) ->
     let i = run_fun output fv n in
     if i < n then Format.printf "Test failed: only %i iterations.\n" i;
     return ()
  | Vnode { init; step } ->
     let i = run_node output init step n in
     if i < n then Format.printf "Test failed: only %i iterations.\n" i;
     return ()
  | _ -> None
 

(* evaluate the main node [main] given by option [-s] for [n] steps *)
(* with check *)
let eval source_name main number to_check =
  let p = parse_implementation_file source_name in
  Debug.print_message "Parsing done";
  flush stdout;
  let p = Scoping.program p in
  Debug.print_message "Scoping done";
  let p = Write.program p in
  Debug.print_message "Write done";
  let* genv = Coiteration.program Primitives.genv0 p in
  Debug.print_message "Evaluation of definitions done";
  match main with
  | None -> return ()
  | Some(main) ->
     Debug.print_message "The main node exists";
     (* make [n] steps and checks that every step returns [true] *)
     if to_check then check genv main number
     else
       (* make [n] steps *)
       run genv main Format.std_formatter number

let eval filename =
  if Filename.check_suffix filename ".zls"
  then 
    begin
      Location.initialize filename;
      let _ = eval filename
                !Smisc.main_node !Smisc.number_of_steps !Smisc.set_check in
     if !Smisc.print_number_of_fixpoint_iterations
      then Format.eprintf
             "@[The number of fixpoint iterations is : %d@]@\n"
             !Smisc.number_of_fixpoint_iterations
    end
  else raise (Arg.Bad "Expected *.zls file.")
    
                                                   
let doc_main = "\tThe main node to evaluate"
let doc_number_of_steps = "\tThe number of steps"
let doc_check = "\tCheck that the simulated node returns true"
let doc_verbose = "\tVerbose mode"
let doc_no_assert = "\tNo check of assertions"
let doc_nocausality = "\tTurn off the check that are variables are non bottom"
let doc_number_of_fixpoint_iterations =
  "\tPrint the number of steps for fixpoints"
    
let errmsg = "Options are:"

let main () =
  try
    Arg.parse (Arg.align
                 [ "-s", Arg.String Smisc.set_main, doc_main;
                   "-n", Arg.Int Smisc.set_number_of_steps, doc_number_of_steps;
                   "-check", Arg.Set Smisc.set_check, doc_check;
                   "-v", Arg.Set set_verbose, doc_verbose;
                   "-noassert", Arg.Set Smisc.no_assert, doc_no_assert;
                   "-nocausality", Arg.Set Smisc.set_nocausality,
                   doc_nocausality;
                   "-fix", Arg.Set Smisc.print_number_of_fixpoint_iterations,
                   doc_number_of_fixpoint_iterations;
                   ])
      eval
      errmsg
  with
  | Error | Stdlib.Exit -> exit 2
  
let _ = main ()
let _ = exit 0
            
