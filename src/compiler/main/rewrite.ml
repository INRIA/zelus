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

(* the main functions *)
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

let default_list =
  ["static", "Static reduction done. See below:",
   Static.program;
   "inline", "Inlining done. See below:",
   Inline.program;
   "der", "Remove handlers in definitions of derivatives. See below:",
   Der.program;
   "auto", "Translation of automata. See below:",
   Automata.program;
   "present", "Translation of present. See below:",
   Present.program;
   "pre", "Compilation of memories (fby/pre) into (init/last). See below:",
   Pre.program;
   "reset", "Compilation of initialization and resets. See below:",
   Reset.program;
   "complete", "Complete equations with [der x = 0.0]. See below:",
   Complete.program;
   "shared",
   "Normalise equations to shared variables in [x = ...]. See below:",
   Shared.program;
   (* "encore", "Add an extra discrete step for weak transitions. See below:",
    Encore.program; *)
   "lastinpatterns",
   "Replace [last x] by [last* m] when [x] is an input variable.\n\
    See below:",
   Lastinpatterns.program;
   "copylast",
   "Add a copy [lx = last* x] to remore false cycles when [x] \n\
    is a local variable. See below:",
   Copylast.program;
   "letin", "Un-nesting of let/in and blocks. See below:",
   Letin.program;
   "schedule", "Static scheduling. See below:",
   Schedule.program ]

(* select the rewritting steps *)
module S = Set.Make (String)
let s_all = List.fold_left (fun acc (s, _, _) -> S.add s acc) S.empty default_list
let s_set = ref s_all
let step_list = ref s_all
let set_steps w =
  let set p s =
    match s with
    | "a" -> s_set := if p then s_all else S.empty
    | "static" | "inline" | "der" | "lastinpatterns" | "copylast"
    | "auto" | "present"
    | "pre" | "reset" | "complete" | "shared" | "encore" | "letin" 
    | "schedule" -> s_set := if p then S.add s !s_set else S.remove s !s_set
    | "" -> ()
    | _ -> raise (Arg.Bad ("unknown pass " ^ s)) in
  let l = String.split_on_char '+' w in
  let l_l = List.map (String.split_on_char '-') l in
  List.iter
    (fun l -> set true (List.hd l); List.iter (fun s -> set false s) (List.tl l))
    l_l
let rewrite_list () =
  List.filter (fun (w, _, _) -> S.mem w !s_set) default_list

let compare name n_steps genv0 p p' =
  Debug.print_message
    ("Checks the pass " ^ name ^
     " for " ^ (string_of_int n_steps) ^" steps\n");
  let genv = Coiteration.program genv0 p in
  let genv' = Coiteration.program genv0 p' in
  Coiteration.check n_steps genv genv'; p'
    
(* Apply a sequence of source-to-source transformation *)
(* do equivalence checking for every step if the flag is turned on *)
let main modname filename n_steps =
  let transform_and_compare genv p (name, comment, transform) =
    let p' = transform genv p in
    print_message comment;
    Debug.print_program p';
    if n_steps = 0 then p' else compare name n_steps genv p p' in
    
  let iter genv p l = List.fold_left (transform_and_compare genv) p l in
  
  let _ = Format.std_formatter in
  
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
  
  (* Associate unique index to variables *)
  let module Scoping = Scoping.Make(Typinfo) in
  let p = do_step "Scoping done. See below:" Debug.print_program
            Scoping.program p in
  (* Write defined variables for equations *)
  let module Write = Write.Make(Typinfo) in
  let p = do_step "Write done. See below: "
      Debug.print_program Write.program p in
  (* Source-to-source transformations start here *)
  let _ = iter genv0 p (rewrite_list ()) in

  apply_with_close_out (fun _ -> ()) otc
