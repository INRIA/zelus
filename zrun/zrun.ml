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

(* The main entry function *)
let run genv main ff n =
  match main with
  | None -> ()
  | Some(main) ->
     let fv =
       find_gvalue_opt (Name main) genv in
     match fv with
     | None -> Format.eprintf "The global value %s is unbound." main
     | Some(fv) ->
        let v = funvalue fv in
        match v with
        | None -> Format.eprintf "The global value %s is not a function." main
        | Some(v) ->
           match v with
           | Vfun(fv) ->
              run_fun (Output.pvalue_and_flush ff) fv n
           | Vnode { init; step } ->
              run_node (Output.pvalue_and_flush ff) init step n
           | _ -> assert false
 
(* evaluate the main node [main] given by option [-s] for [n_steps] steps *)
let eval filename main n_steps =
  (* standard output *)
  let info_ff = Format.formatter_of_out_channel stdout in
  Format.pp_set_max_boxes info_ff max_int;

  (* standard error *)
  let err_ff = Format.formatter_of_out_channel stderr in
  Format.pp_set_max_boxes err_ff max_int;

  let do_step comment step input = 
    let output = step input in
    Sdebug.print_message comment;
    Printer.program info_ff output;
    output in

  let impl_list = parse_implementation_file filename in
  Debug.print_message "Parsing done";

  (* Scoping *)
  let impl_list = (* do_step "Scoping done" *) Scoping.program impl_list in

  (* Write defined variables for equations *)
  let impl_list = do_step "Write done" Write.program impl_list in

  (* Evaluation of definitions in [filename] *)
  let genv = Opt.get (Coiteration.program Primitives.genv0 impl_list) in
  Debug.print_message "Evaluation of definitions done";

  (* Evaluate [f ()] or [run f ()] *)
  run genv main Format.std_formatter n_steps

let main filename =
  if Filename.check_suffix filename ".zls"
  then 
    begin
      Location.initialize filename;
      let _ = eval filename !Smisc.main_node !Smisc.number_of_steps in
     if !Smisc.print_number_of_fixpoint_iterations
      then Format.eprintf
             "@[The number of fixpoint iterations is : %d@]@\n"
             !Smisc.number_of_fixpoint_iterations
    end
  else raise (Arg.Bad "Expected *.zls file.")
    
                                                   
let doc_main = "\tThe main node to evaluate"
let doc_number_of_steps = "\tThe number of steps"
let doc_verbose = "\tVerbose mode"
let doc_vverbose = "\t Set even more verbose mode"
let doc_no_assert = "\tNo check of assertions"
let doc_nocausality = "\tTurn off the check that are variables are non bottom"
let doc_number_of_fixpoint_iterations =
  "\tPrint the number of steps for fixpoints"
    
let errmsg = "Options are:"

let set_verbose () =
  let open Misc in
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  let open Misc in
  vverbose := true;
  set_verbose ()

let main () =
  try
    Arg.parse (Arg.align
                 [ "-s", Arg.String Smisc.set_main, doc_main;
                   "-n", Arg.Int Smisc.set_number_of_steps, doc_number_of_steps;
                   "-v", Arg.Unit set_verbose, doc_verbose;
                   "-vv", Arg.Unit set_vverbose, doc_vverbose;
                   "-noassert", Arg.Set Smisc.no_assert, doc_no_assert;
                   "-nocausality", Arg.Set Smisc.set_nocausality,
                   doc_nocausality;
                   "-fix", Arg.Set Smisc.print_number_of_fixpoint_iterations,
                   doc_number_of_fixpoint_iterations;
                   ])
      main
      errmsg
  with
  | Error | Stdlib.Exit -> exit 2
  
let _ = main ()
let _ = exit 0
            
