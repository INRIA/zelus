(* Warning: *)	
(* This file is based on the original version of ocamldep.ml *)	
(* from the Objective Caml 3.12 distribution, INRIA          *)	

(***********************************************************************)	
(*                                                                     *)	
(*                           Objective Caml                            *)	
(*                                                                     *)	
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)	
(*                                                                     *)	
(*  Copyright 1999 Institut National de Recherche en Informatique et   *)	
(*  en Automatique.  All rights reserved.  This file is distributed    *)	
(*  under the terms of the Q Public License version 1.0.               *)	
(*                                                                     *)	
(***********************************************************************)	

open Deps_tools
open Compiler
open Format	

type file_kind = ZLS | ZLI;;	

let file_dependencies_as kind source_file =	
  try	
    if Sys.file_exists source_file then begin	
      match kind with	
      | ZLS -> zls_file_dependencies source_file	
      | ZLI -> zli_file_dependencies source_file	
    end	
  with x ->	
    let report_err = function	
    | Zlexer.Lexical_error (err, range) ->
        (* fprintf Format.err_formatter "@[%a%a@]@." *)	
          lexical_error err range	
    | Zparser.Error ->
        (* fprintf Format.err_formatter "@[%a@]@." *)	
          (* syntax_error (Loc(Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf)) *) ()	
    | Sys_error msg ->	
        fprintf Format.err_formatter "@[I/O error:@ %s@]@." msg	
    | Preprocessing_error ->	
        fprintf Format.err_formatter "@[Preprocessing error on file %s@]@."	
            source_file	
    | x -> raise x in	
    error_occurred := true;	
    report_err x	

let file_dependencies source_file =	
  if Filename.check_suffix source_file ".zls" then	
    file_dependencies_as ZLS source_file	
  else if Filename.check_suffix source_file ".zli" then	
    file_dependencies_as ZLI source_file	
  else ()

(* Entry point *)	

let usage = "Usage: zlsdep [options] <source files>\nOptions are:"	

let _ =	
  try
    add_to_load_path Filename.current_dir_name;
    Arg.parse [
       "-I", Arg.String add_to_load_path,
         "<dir>  Add <dir> to the list of include directories";
       "-impl", Arg.String (file_dependencies_as ZLS),
         "<f> Process <f> as a .zls file";
       "-intf", Arg.String (file_dependencies_as ZLI),
         "<f> Process <f> as a .zli file";
       "-pp", Arg.String(fun s -> preprocessor := Some s),
         "<cmd> Pipe sources through preprocessor <cmd>";
       "-slash", Arg.Set force_slash,
         "   (Windows) Use forward slash / instead of backslash \\ in file paths";
      ] file_dependencies usage;
    exit (if !error_occurred then 2 else 0)
  with
  | Zmisc.Error -> exit 2;;
