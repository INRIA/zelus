(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the main functions *)
open Misc
open Location
open Monad
open Result
open Value
open Lident
open Find
open Primitives
open Error
open Coiteration
               
exception Stop

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
               
           
let apply_with_close_out f o =
  try
    f o;
    close_out o
  with x -> close_out o; raise x

let do_step comment output step input = 
  let o = step input in
  Debug.print_message comment;
  output o;
  o


(* Evaluate all the definition in a file, store values *)
let main modname filename n_steps is_all l_names =
  let open Genv in
  let ff = Format.std_formatter in
  (* output file in which values are stored *)
  let obj_name = filename ^ ".zlo" in
  let otc = open_out_bin obj_name in
  let source_name = filename ^ ".zls" in

  (* set the current opened module *)
  Location.initialize source_name;

  (* Parsing *)
  let p = parse_implementation_file source_name in
  Debug.print_message "Parsing done";

  (* defines the initial global environment for values *)
  let genv0 = Genv.initialize modname [] in
  (* Add Stdlib *)
  let genv0 = Genv.add_module genv0 (Primitives.stdlib_env ()) in
  
  let module Scoping = Scoping.Make(Noinfo) in
  (* Associate unique index to variables *)
  let p = do_step "Scoping done" Debug.print_program Scoping.program p in
  let module Write = Write.Make(Noinfo) in
  (* Write defined variables for equations *)
  let p = do_step "Write done" Debug.print_program Write.program p in

  (* Evaluation of definitions *)
  let genv = do_step "Evaluation of definitions done"
      Debug.print_nothing (Coiteration.program genv0) p in
  
  (* Write the values into a file *)
  apply_with_close_out (Genv.write genv) otc;

  (* evaluate a list of main function/nodes *)
  if is_all then Coiteration.all ff n_steps (Genv.current genv)
  else Coiteration.eval_list ff n_steps genv l_names

