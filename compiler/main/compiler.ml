(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(** The compiler *)
open Location
open Misc
open Global
open Zelus
open Format

let lexical_error err loc =
  eprintf "%aIllegal character.@." output_location loc;
  raise Error

let syntax_error loc =
  eprintf "%aSyntax error.@." output_location loc;
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

let compile_interface parse modname filename suffix =
  (* input and outputs *)
  let source_name = filename ^ suffix
  and obj_interf_name = filename ^ ".lci" in
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

(* compiling an interface *)
let interface modname filename =
  compile_interface parse_interface_file modname filename ".lsi"

(* select which source-to-source transformation to remove ODEs *)
let dselect impl_list =
  match !hybrid_mode with
    | DeltadelayTuple  -> Ode.implementation_list impl_list
    | _ -> 
        eprintf "The requested hybrid translation is not yet implemented.";
        raise Error

let apply_with_close_out f o =
  try
    f o;
    close_out o
  with x -> close_out o; raise x
        
(** The main function for compiling a program *)
let compile modname filename =
  (* input and output files *)
  let source_name = filename ^ ".ls"
  and obj_interf_name = filename ^ ".lci"
  and ml_name = filename ^ ".ml" in

  (* standard output for printing types and clocks *)
  let info_ff = Format.formatter_of_out_channel stdout in
  pp_set_max_boxes info_ff max_int;

  let write_implementation_list impl_list mlc =
    let mlc_ff = Format.formatter_of_out_channel mlc in
    pp_set_max_boxes mlc_ff max_int;
    Oprinter.implementation_list mlc_ff true impl_list in

  let comment c =
    let sep =
"----------------------------------------------------------------------------"in
    fprintf info_ff "%s@\n%s@\n%s@." sep c sep in

  Modules.initialize modname;
  Location.initialize source_name;

  (* Parsing of the file *)
  let impl_list = parse_implementation_file source_name in
  if !verbose then comment "Parsing done. See below:";

  (* Scoping *)
  let impl_list = Scoping.implementation_list impl_list in
  if !verbose then comment "Scoping done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* Typing *)
  Typing.implementation_list info_ff impl_list;
  if !verbose then comment "Typing done.";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* continue if [typeonly = false] *)
  if not !typeonly then begin

  (* Causality check *)
  if not (!Misc.no_causality) then
    begin
      if !Misc.causality
      then Causality.implementation_list info_ff impl_list
      else Newcausality.implementation_list info_ff impl_list;
      if !verbose then comment "Causality check done"
    end;

  (* Initialization check *)
  if not (!Misc.no_initialisation) then
    begin Initialization.implementation_list info_ff impl_list;
      if !verbose then comment "Initialization check done"
    end;

  (* Start of source-to-source translation *)
  
  (* Elimation of automata *)
  let impl_list = Automata.implementation_list impl_list in
  if !verbose then comment "Translation of automata done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* Elimation of activations *)
  let impl_list = Activate.implementation_list impl_list in
  if !verbose then comment "Translation of activations done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* Static expansion of function calls (inlining) *)
  (* inlined code is stored into a global symbol table *)
  let impl_list = Inline.implementation_list impl_list in
  if !verbose then comment "Inlining of function calls. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* From now on, only functions declared atomic are compiled *)
  (* others have been removed from the list of functions *)
    
  (* normalise the structure of let/ins with state to simplify later steps *)
  let impl_list = Letin.implementation_list true impl_list in
  if !verbose then comment 
    "Flattening lets and naming of stateful applications done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* compilation of periods into ODEs *)
  let impl_list = if !Misc.compile_periods_into_discrete_counters
    then begin (* ... discrete counters *)
      let impl_list = Period.implementation_list impl_list in
      if !verbose then comment "Translation of periods done. See below:";
      if !verbose then Printer.implementation_list info_ff impl_list;
      impl_list
    end else 
      begin (* ... ODEs with reset *)
        let impl_list = Periodz.implementation_list impl_list in
        if !verbose then 
          comment "Translation of periods into zero-crossing done. See below:";
        if !verbose then Printer.implementation_list info_ff impl_list;
        impl_list
      end in

  (* Insertion of goagain wires for making one more transition *)
  let impl_list = Goagain.implementation_list impl_list in
  if !verbose then comment "Add goagains for weak transitions. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
    
  (* Elimination of presents. *)
  let impl_list = Present.implementation_list impl_list in
  if !verbose then comment "Translation of present done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* actualize the set of write variable in every block *)
  let impl_list = Write.implementation_list impl_list in
  if !verbose then comment 
    "Actualize write variables in blocks. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  let impl_list = Completion.implementation_list impl_list in
  if !verbose then 
    comment "Completion and naming of shared variables done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* removal of ODEs *)
  let impl_list = dselect impl_list in
  if !verbose then comment "Removal of ODEs done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* sequential code generation starts here *)

  (* compile the reset construct. Introduce a fresh reset for every branch *)
  let impl_list = Reset.implementation_list impl_list in
  if !verbose then 
    comment 
  "Compilation of reset done. Add initialization bit for every branch. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* normalise the structure of let/ins with state to simplify later steps *)
  let impl_list = Letin.implementation_list false impl_list in
  if !verbose then comment 
    "Flattening lets and naming of stateful applications done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* actualize the set of write variable in every block *)
  let impl_list = Write.implementation_list impl_list in
  if !verbose then comment 
    "Actualize write variables in blocks. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* remove pattern assignments to shared variables *)
  (* and complete partial definitions with equations of the form [x = last x] *)
  let impl_list = Completion.implementation_list impl_list in
  if !verbose then 
    comment "Completion and naming of shared variables done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* compiling various forms of memories (init/->/last/fby/pre) *)
  let impl_list = Last.implementation_list impl_list in
  if !verbose then 
    comment "Compilation of memories (init/->/last/fby/pre). See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* actualize the set of write variable in every block *)
  let impl_list = Write.implementation_list impl_list in
  if !verbose then comment 
    "Actualize write variables in blocks. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* A-normal form. A restricted case for the moment. *)
  let impl_list = Aform.implementation_list impl_list in
  if !verbose then 
    comment "Translation into A-normal form. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;

  (* optimization. cse elimination *)
  let impl_list = Cse.implementation_list impl_list in
  if !verbose then 
    comment "Common sub-expression elimination for registers. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* schedule *)
  let impl_list = Schedule.implementation_list impl_list in
  if !verbose then comment "Scheduling done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* remove copy variables *)
  let impl_list = Copy.implementation_list impl_list in
  if !verbose then comment "Removing of copy variables done. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* optimization. dead-code removal *)
  let impl_list = Deadcode.implementation_list impl_list in
  if !verbose then comment "Deadcode removal. See below:";
  if !verbose then Printer.implementation_list info_ff impl_list;
  
  (* translate *)
  let impl_list = Translate.implementation_list impl_list in
  if !verbose then comment "Translation done. See below:";
  if !verbose then Oprinter.implementation_list info_ff false impl_list;
  
  (* generate ml code *)
  let mlc = open_out ml_name in
  apply_with_close_out (write_implementation_list impl_list) mlc;

  end;

  (* Write the symbol table into the interface file *)
  let itc = open_out_bin obj_interf_name in
  apply_with_close_out Modules.write itc

