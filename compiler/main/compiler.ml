(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
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
        
(** The main function for compiling a program *)
let compile modname filename =
  (* input and output files *)
  let source_name = filename ^ ".zls"
  and obj_interf_name = filename ^ ".zci"
  and ml_name = filename ^ ".ml"
  and lmm_name = filename ^ ".lmm" in

  (* standard output for printing types and clocks *)
  let info_ff = Format.formatter_of_out_channel stdout in
  pp_set_max_boxes info_ff max_int;

  let write_implementation_list obc_list mlc =
    let mlc_ff = Format.formatter_of_out_channel mlc in
    pp_set_max_boxes mlc_ff max_int;
    Ocamlprinter.implementation_list mlc_ff obc_list in

  let write_lmm_list impl_list lmmc =
    let lmm_ff = Format.formatter_of_out_channel lmmc in
    pp_set_max_boxes lmm_ff max_int;
    Plmm.implementation_list lmm_ff impl_list in

  Modules.initialize modname;
  Location.initialize source_name;

  let comment c =
  let sep =
  "----------------------------------------------------------------------------"in
    fprintf info_ff "%s@\n%s@\n%s@." sep c sep in

  (* execute a rewrite step *)
  let step com step impl_list =
    let impl_list = step impl_list in
    if !verbose then
      begin comment com; Printer.implementation_list info_ff impl_list end;
    impl_list in

  (* Parsing of the file *)
  let impl_list = parse_implementation_file source_name in
  if !verbose then comment "Parsing done. See below:";
  
  let impl_list =
    step "Scoping done. See below:" Scoping.implementation_list impl_list in
  let impl_list =
    step "Typing done." (Typing.implementation_list info_ff true) impl_list in
  let impl_list =
    if not !no_causality
    then step "Causality check done"
	(Causality.implementation_list info_ff) impl_list
    else impl_list in
  let impl_list =
    if not !no_initialisation
    then step "Initialization check done"
	(Initialization.implementation_list info_ff) impl_list
    else impl_list in
  if not !typeonly then
    begin
      (* continue if [typeonly = false] *)
      (* Start of source-to-source translation *)
      let impl_list =
	step "Mark functions calls to be inlined. See below:"
	     Markfunctions.implementation_list impl_list in
      let impl_list =
	step "Reduce static expressions for global values \
              that have no more static parameter. See below:"
	     (Reduce.implementation_list info_ff) impl_list in
      let impl_list =
	step "Inlining of annotated and small function calls. See below:"
	     Inline.implementation_list impl_list in
      let impl_list =
	step "Re-typing done. See below:"
	     (Typing.implementation_list info_ff false) impl_list in
      let impl_list =
        step "Remove last in pattern. See below:"
	     Remove_last_in_patterns.implementation_list impl_list in
      let impl_list =
        step "Add a copy for [last x] to remore false cycles. See below:"
	     Add_copy_for_last.implementation_list impl_list in
      let impl_list =
	step "Translation of automata done. See below:"
	     Automata.implementation_list impl_list in
      let impl_list =
	step "Translation of activations done. See below:"
	     Activate.implementation_list impl_list in
      let impl_list =
	step "Translation of present done. See below:"
	     Present.implementation_list impl_list in
      let impl_list =
	step "Translation of periods done. See below:"
	     Period.implementation_list impl_list in
      let impl_list =
	step "Translation of disc done. See below:"
	     Disc.implementation_list impl_list in
      let impl_list =
	step "Translation of probabilistic nodes. See below:"
	     Proba.implementation_list impl_list in
      let impl_list =
	step
	  "Compilation of memories (fby/pre/next) into (init/last). See below:"
	     Pre.implementation_list impl_list in
      let impl_list =
	step "Un-nest let/in blocks. See below:"
	     Letin.implementation_list impl_list in
      let impl_list =
	step "Compilation of initialization and resets done. See below:"
	     Reset.implementation_list impl_list in
      let impl_list =
	step "Actualize write variables in blocks. See below:"
	     Write.implementation_list impl_list in
      let impl_list =
	step "Complete equations with [der x = 0.0]. See below:"
	    Complete.implementation_list impl_list in
     let impl_list =
	step "Add an extra discrete step for weak transitions. See below:"
	    Encore.implementation_list impl_list in
     let impl_list =
	step "Gather all horizons into a single one per function. See below:"
	    Horizon.implementation_list impl_list in
     let impl_list =
       step "Translation into A-normal form. See below:"
	    Aform.implementation_list impl_list in
     let impl_list =
	step "Actualize write variables in blocks. See below:"
	     Write.implementation_list impl_list in
     let impl_list =
       step "Naming shared variables and memories done. See below:"
	    Shared.implementation_list impl_list in
     let impl_list =
       step "Common sub-expression elimination. See below:"
	    Cse.implementation_list impl_list in
     let impl_list =
       step "Sharing of zero-crossings. See below:"
	    Zopt.implementation_list impl_list in
     let impl_list =
       step "Actualize write variables in blocks. See below:"
	    Write.implementation_list impl_list in
     let impl_list =
       if not !no_opt && not !no_deadcode
       then step "Deadcode removal. See below:"
		 Deadcode.implementation_list impl_list
       else impl_list in
     let impl_list =
       step "Static scheduling done. See below:"
	    Schedule.implementation_list impl_list in
     let impl_list =
       if not !no_opt && not !no_deadcode
       then
	 let impl_list =
	   step "Removing of copy variables done. See below:"
		Copy.implementation_list impl_list in
	 step "Deadcode removal. See below:"
	      Deadcode.implementation_list impl_list
       else impl_list in
     (* start of translation into sequential code *)
     let obc_list =
       Translate.implementation_list impl_list in
     if !verbose
     then begin
	 comment "Translation done. See below:";
	 Oprinter.implementation_list info_ff obc_list
       end;
     let obc_list = Inout.implementation_list obc_list in
     if !verbose
     then begin
	 comment "Add code to read/write continuous states and zero-crossings \
                  vectors. See below:";
         Oprinter.implementation_list info_ff obc_list
       end;
     (* print OCaml code *)
     if !verbose
     then begin
	 comment "Print OCaml code. See below:";
	 Ocamlprinter.implementation_list info_ff obc_list
       end;
     (* write OCaml code in the appropriate file *)
     let mlc = open_out ml_name in
     apply_with_close_out (write_implementation_list obc_list) mlc;     
     (* Write the symbol table into the interface file *)
     let itc = open_out_bin obj_interf_name in
     apply_with_close_out Modules.write itc;

     (* translate into L-- if asked for *)
     if Misc.S.is_empty !Misc.lmm_nodes then ()
     else
       let impl_list =
	step "Rewrite of pattern matchings into primitive ones done. See below:"
	     Match2condition.implementation_list impl_list in
       let lmm_list =
         Zlus2lmm.implementation_list !Misc.lmm_nodes impl_list in
       if lmm_list <> [] then
         let lmm = open_out lmm_name in
         apply_with_close_out (write_lmm_list lmm_list) lmm
    end
