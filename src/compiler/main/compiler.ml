(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the compiler *)
open Misc
open Location
               
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
  Format.pp_set_max_boxes info_ff max_int;

  let close_all_files () =
    close_out itc in

  try
    Modules.initialize modname;
    Location.initialize source_name;

    (* Parsing of the file *)
    let l = parse source_name in
    (* Scoping *)
    let module Scoping = Scoping.Make(Typinfo) in
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

let print_message comment =
  if !verbose then
    Format.fprintf Format.err_formatter
      "@[------------------------------------------------------------------\n\
       %s\n\
       --------------------------------------------------------------------@]@."
      comment

let do_step comment output step input = 
  print_message comment;
  let o = step input in
  output o;
  o

let do_optional_step no_step comment output step input = 
  if no_step then input else do_step comment output step input

(* The main function for compiling a program *)
let compile modname filename =
  let source_name = filename ^ ".zls" in
  let obj_interf_name = filename ^ ".zci" in

  (* standard output for printing types *)
  let info_ff = Format.formatter_of_out_channel stdout in
  Format.pp_set_max_boxes info_ff max_int;

  (* set the current opened module *)
  Modules.initialize modname;
  Location.initialize source_name;

  (* Parsing *)
  let p = parse_implementation_file source_name in
  Debug.print_message "Parsing done";

  try
    (* Associate unique index to variables *)
    let module Scoping = Scoping.Make(Typinfo) in
    let p = do_step "Scoping done. See below:" Debug.print_program
              Scoping.program p in
    (* Write defined variables for equations *)
    let module Write = Write.Make(Typinfo) in
    let p = do_step "Write done. See below: "
              Debug.print_program Write.program p in
    if !parseonly then raise Stop;
    let p = do_step "Typing done. See below:" Debug.print_program
              (Typing.program info_ff true) p in
    let p = do_optional_step !Misc.no_causality "Causality done. See below:"
              Debug.print_program (Causality.program info_ff) p in
    let _ = do_optional_step
              !Misc.no_initialization "Initialization done. See below:"
              Debug.print_program (Initialization.program info_ff) p in
    (* Write the symbol table into the interface file *)
    let itc = open_out_bin obj_interf_name in
    if !Misc.typeonly then raise Stop;
    apply_with_close_out Modules.write itc
  with
  | Stop -> ()
