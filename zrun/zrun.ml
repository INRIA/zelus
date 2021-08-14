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
open Smisc
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
               
(* The main entry function. Execute [n] steps of [main()] or [run main ()]  *)
let eval_main genv main n_steps =
  match main with
  | None -> ()
  | Some(main) ->
     let fv =
       find_gvalue_opt (Name main) genv in
     match fv with
     | None -> Format.eprintf "The global value %s is unbound.\n" main
     | Some(fv) ->
        let v = to_fun fv in
        match v with
        | None ->
           Format.eprintf "The global value %s is not a function.\n" main
        | Some(v) ->
           let output v =
             Output.pvalue_flush Format.std_formatter v in
           match v with
           | Vfun(fv) ->
              run_fun output fv n_steps
           | Vnode { init; step } ->
              run_node output init step n_steps
           | _ -> assert false

let apply_with_close_out f o =
  try
    f o;
    close_out o
  with x -> close_out o; raise x

let do_step comment step input = 
  let output = step input in
  Debug.print_message comment;
  Debug.print_program output;
  output

(* Evaluate all the definition in a file, store values *)
(* and a main function/node, if given *)
let eval_file modname filename suffix main n_steps =
  (* output file in which values are stored *)
  (*
    let obj_name = filename ^ ".zlo" in
    let otc = open_out_bin obj_name in
   *)
  
  let source_name = filename ^ suffix in

  Location.initialize source_name;

  (* Parsing *)
  let impl_list = parse_implementation_file source_name in
  Debug.print_message "Parsing done";

  (* Scoping *)
  let impl_list = (* do_step "Scoping done" *) Scoping.program impl_list in

  (* Write defined variables for equations *)
  let impl_list = do_step "Write done" Write.program impl_list in

  (* Evaluation of definitions in [filename] *)
  let genv = Genv.initialize modname [] in
  (* Add Stdlib *)
  let genv = Genv.add_module genv Primitives.stdlib_env in
  
  let genv = Opt.get (Coiteration.program genv impl_list) in
  Debug.print_message "Evaluation of definitions done";

  (* Write the values into a file *)
  (* 
    TODO
    apply_with_close_out (Genv.write genv) otc;
   *)

  (* evaluate a main function/node if given *)
  eval_main genv main n_steps
             
let main file =
  if Filename.check_suffix file ".zls"
  then 
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    eval_file modname filename ".zls" !Smisc.main_node !Smisc.number_of_steps
  else raise (Arg.Bad "Expected *.zls file.")
                                                       
let doc_main = "\tThe main node to evaluate"
let doc_number_of_steps = "\tThe number of steps"
let doc_verbose = "\tVerbose mode"
let doc_vverbose = "\t Set even more verbose mode"
let doc_no_assert = "\tNo check of assertions"
let doc_nocausality = "\tTurn off the check that are variables are non bottom"
let doc_print_values = "\tPrint values"
let doc_number_of_fixpoint_iterations =
  "\tPrint the number of steps for fixpoints"
    
let errmsg = "Options are:"


let main () =
  try
    Arg.parse
      (Arg.align
         [ "-s", Arg.String Smisc.set_main, doc_main;
           "-n", Arg.Int Smisc.set_number_of_steps, doc_number_of_steps;
           "-v", Arg.Unit set_verbose, doc_verbose;
           "-vv", Arg.Unit set_vverbose, doc_vverbose;
           "-iv", Arg.Set print_values, doc_print_values;
           "-noassert", Arg.Set Smisc.no_assert, doc_no_assert;
           "-nocausality", Arg.Set Smisc.set_nocausality, doc_nocausality;
           "-fix", Arg.Set Smisc.print_number_of_fixpoint_iterations,
           doc_number_of_fixpoint_iterations;
      ])
      main
      errmsg
  with
  | Stdlib.Exit -> exit 2
  
let _ = main ()
let _ = exit 0
            
