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
let eval_main genv n_steps is_check main =
  let fv =
    find_gvalue_opt (Name main) genv in
  match fv with
  | None ->
     Format.eprintf "The global value %s is unbound.\n" main;
     raise Stdlib.Exit
  | Some(fv) ->
     let v = to_fun fv in
     match v with
     | None ->
        Format.eprintf "The global value %s is not a function.\n" main;
        raise Stdlib.Exit
     | Some(v) ->
        let output =
          if is_check then
            fun v -> if (v = Vbool(true)) then () else raise Stdlib.Exit
          else
            fun v -> Output.pvalue_flush Format.std_formatter v in
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
let file modname filename n_steps is_check main_nodes =
  (* output file in which values are stored *)
  let obj_name = filename ^ ".zlo" in
  let otc = open_out_bin obj_name in
    
  let source_name = filename ^ ".zls" in

  Location.initialize source_name;

  (* Parsing *)
  let impl_list = parse_implementation_file source_name in
  Debug.print_message "Parsing done";

  (* Scoping *)
  let impl_list = Scoping.program impl_list in
  Debug.print_message "Scoping done";
  
  (* Write defined variables for equations *)
  let impl_list = do_step "Write done" Write.program impl_list in

  (* Evaluation of definitions in [filename] *)
  let genv = Genv.initialize modname [] in
  (* Add Stdlib *)
  let genv = Genv.add_module genv Primitives.stdlib_env in
  
  let genv = Opt.get (Coiteration.program genv impl_list) in
  Debug.print_message "Evaluation of definitions done";

  (* Write the values into a file *)
  (* Genv.write genv otc; *)
  apply_with_close_out (Genv.write genv) otc;
  
  (* evaluate a list of main function/nodes *)
  List.iter (eval_main genv n_steps is_check) main_nodes
             
