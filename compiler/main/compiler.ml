(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(** The compiler *)
open Location
open Misc
open Global
open Zelus
open Format

let lexical_error err loc =
  eprintf "%aIllegal character.@." output_location loc;
  raise Stdlib.Exit

let syntax_error loc =
  eprintf "%aSyntax error.@." output_location loc;
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

let parse_interface_file source_name =
  parse Parser.interface_file Lexer.main source_name

let parse_scalar_interface_file source_name =
  parse Parser.scalar_interface_file Lexer.main source_name

let compile_interface parse modname filename suffix =
  (* input and outputs *)
  let source_name = filename ^ suffix
  and obj_interf_name = filename ^ ".zci" in
  let itc = open_out_bin obj_interf_name in
  let info_ff = Format.formatter_of_out_channel stdout in
  pp_set_max_boxes info_ff max_int;

  let close_all_files () =
    close_out itc in

  try
    Modules.initialize modname;
    Location.initialize source_name;

    (* Parsing of the file *)
    let l = parse source_name in
    (* Scoping *)
    let l = Scoping.interface_list l in
    Interface.interface_list info_ff l;
    (* Write the symbol table into the interface file *)
    Modules.write itc;
    close_all_files ()
  with
  | x -> close_all_files (); raise x

(* compiling a scalar interface *)
let scalar_interface modname filename =
  compile_interface parse_scalar_interface_file modname filename ".mli"

(* compiling a Zelus interface *)
let interface modname filename =
  compile_interface parse_interface_file modname filename ".zli"

let apply_with_close_out f o =
  try
    f o;
    close_out o
  with x -> close_out o; raise x

(** Make a compiler step **)
let do_step comment step input = 
  let output = step input in
  Debug.print_message comment;
  Debug.print_program output;
  output
  
let do_optional_step is_step comment step p = 
  if is_step then do_step comment step p else p

(** The main function for compiling a program *)
let compile modname filename =
  (* input and output files *)
  let source_name = filename ^ ".zls" in
  let obj_interf_name = filename ^ ".zci" in

  (* standard output for printing types and clocks *)
  let info_ff = Format.formatter_of_out_channel stdout in
  pp_set_max_boxes info_ff max_int;

  (* set the current opened module and open default modules *)
  Modules.initialize modname;
  (* set the current opened module *)
  Location.initialize source_name;

  (* Parsing of the file *)
  let impl_list = parse_implementation_file source_name in
  Debug.print_message "Parsing done";
  (* Scoping *)
  impl_list
  |> do_step "Scoping done" Scoping.program
  (* Write defined variables for equations *)
  |> do_step "Write done" Write.program
  (* Typing *)
  |> do_step "Typing done" (Typing.program info_ff true)
  (* Causality *)
  |> do_optional_step (not !no_causality)
       "Causality done" (Causality.program info_ff)
  (* Initialization *)
  |> do_optional_step (not !no_initialization)
       "Initialisation done" (Initialization.program info_ff)
  |> fun _ -> ();
  (* Write the symbol table into the interface file *)
  let itc = open_out_bin obj_interf_name in
  apply_with_close_out Modules.write itc;
