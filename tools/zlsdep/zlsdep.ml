(**********************************************************************)
(*                                                                    *)
(*                           ReactiveML                               *)
(*                    http://reactiveML.org                           *)
(*                    http://rml.inria.fr                             *)
(*                                                                    *)
(*                          Louis Mandel                              *)
(*                                                                    *)
(*  Copyright 2002, 2007 Louis Mandel.  All rights reserved.          *)
(*  This file is distributed under the terms of the Q Public License  *)
(*  version 1.0.                                                      *)
(*                                                                    *)
(*  ReactiveML has been done in the following labs:                   *)
(*  - theme SPI, Laboratoire d'Informatique de Paris 6 (2002-2005)    *)
(*  - Verimag, CNRS Grenoble (2005-2006)                              *)
(*  - projet Moscova, INRIA Rocquencourt (2006-2007)                  *)
(*                                                                    *)
(**********************************************************************)

(* file: rmldep.ml *)

(* Warning: *)
(* This file is based on the original version of ocamldep.ml *)
(* from the Objective Caml 3.12 distribution, INRIA          *)

(* first modification: 2007-02-16 *)
(* modified by: Louis Mandel      *)

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

(* $Id$ *)

open Format
open Location
open Parsetree
open Misc


(* Print the dependencies *)

let load_path = ref ([] : (string * string array) list)
let ml_synonyms = ref [".ml"; ".zls"; ".mly"; ".mll"]
let mli_synonyms = ref [".mli"; ".zli"; ".mly"]
let native_only = ref false
let force_slash = ref false
let error_occurred = ref false
let raw_dependencies = ref false

(* Fix path to use '/' as directory separator instead of '\'.
   Only under Windows. *)

let fix_slash s =
  if Sys.os_type = "Unix" then s else begin
    let r = String.copy s in
    for i = 0 to String.length r - 1 do
      if r.[i] = '\\' then r.[i] <- '/'
    done;
    r
  end

let expand_directory alt s =
  if String.length s > 0 && s.[0] = '+'
  then Filename.concat alt
                       (String.sub s 1 (String.length s - 1))
  else s

let remove_file filename =
  try
    Sys.remove filename
  with Sys_error msg ->
    ()

let add_to_load_path dir =
  try
    let dir = expand_directory "../../lib" dir in
    let contents = Sys.readdir dir in
    load_path := !load_path @ [dir, contents]
  with Sys_error msg ->
    fprintf Format.err_formatter "@[Bad -I option: %s@]@." msg;
    error_occurred := true

let add_to_synonym_list synonyms suffix =
  if (String.length suffix) > 1 && suffix.[0] = '.' then
    synonyms := suffix :: !synonyms
  else begin
    fprintf Format.err_formatter "@[Bad suffix: '%s'@]@." suffix;
    error_occurred := true
  end

let find_file name =
  let uname = String.uncapitalize name in
  let rec find_in_array a pos =
    if pos >= Array.length a then None else begin
      let s = a.(pos) in
      if s = name || s = uname then Some s else find_in_array a (pos + 1)
    end in
  let rec find_in_path = function
    [] -> raise Not_found
  | (dir, contents) :: rem ->
      match find_in_array contents 0 with
        Some truename ->
          if dir = "." then truename else Filename.concat dir truename
      | None -> find_in_path rem in
  find_in_path !load_path

let rec find_file_in_list = function
  [] -> raise Not_found
| x :: rem -> try find_file x with Not_found -> find_file_in_list rem

let find_dependency modname (byt_deps, opt_deps) =
  try
    let candidates = List.map ((^) modname) !mli_synonyms in
    let filename = find_file_in_list candidates in
    let basename = Filename.chop_extension filename in
    let optname =
      if List.exists (fun ext -> Sys.file_exists (basename ^ ext)) !ml_synonyms
      then basename ^ ".ml"
      else basename ^ ".zci" in
    ((basename ^ ".zci") :: byt_deps, optname :: opt_deps)
  with Not_found ->
  try
    let candidates = List.map ((^) modname) !ml_synonyms in
    let filename = find_file_in_list candidates in
    let basename = Filename.chop_extension filename in
    ( (basename^".ml") :: byt_deps, (basename ^ ".ml") :: opt_deps)
  with Not_found ->
    (byt_deps, opt_deps)

let (depends_on, escaped_eol) = (":", " \\\n    ")

let print_filename s =
  let s = if !force_slash then fix_slash s else s in
  if not (String.contains s ' ') then begin
    print_string s;
  end else begin
    let rec count n i =
      if i >= String.length s then n
      else if s.[i] = ' ' then count (n+1) (i+1)
      else count n (i+1)
    in
    let spaces = count 0 0 in
    let result = String.create (String.length s + spaces) in
    let rec loop i j =
      if i >= String.length s then ()
      else if s.[i] = ' ' then begin
        result.[j] <- '\\';
        result.[j+1] <- ' ';
        loop (i+1) (j+2);
      end else begin
        result.[j] <- s.[i];
        loop (i+1) (j+1);
      end
    in
    loop 0 0;
    print_string result;
  end
;;

let print_dependencies target_file deps =
  print_filename target_file; print_string depends_on;
  let rec print_items pos = function
    [] -> print_string "\n"
  | dep :: rem ->
      if pos + 1 + String.length dep <= 77 then begin
        print_string " "; print_filename dep;
        print_items (pos + String.length dep + 1) rem
      end else begin
        print_string escaped_eol; print_filename dep;
        print_items (String.length dep + 4) rem
      end in
  print_items (String.length target_file + 1) deps

let print_raw_dependencies source_file deps =
  print_filename source_file; print_string ":";
  Depend.StringSet.iter
    (fun dep ->
      if (String.length dep > 0)
          && (match dep.[0] with 'A'..'Z' -> true | _ -> false) then begin
            print_char ' ';
            print_string dep
          end)
    deps;
  print_char '\n'

(* Optionally preprocess a source file *)

let preprocessor = ref None

exception Preprocessing_error

let preprocess sourcefile =
  match !preprocessor with
    None -> sourcefile
  | Some pp ->
      flush Pervasives.stdout;
      let tmpfile = Filename.temp_file "camlpp" "" in
      let comm = Printf.sprintf "%s %s > %s" pp sourcefile tmpfile in
      if Sys.command comm <> 0 then begin
        remove_file tmpfile;
        raise Preprocessing_error
      end;
      tmpfile

let remove_preprocessed inputfile =
  match !preprocessor with
    None -> ()
  | Some _ -> remove_file inputfile

(* Parse a file or get a dumped syntax tree in it *)

let lexical_error err loc =
  eprintf "%aIllegal character.@." output_location loc;
  raise Error

let syntax_error loc =
  eprintf "%aSyntax error.@." output_location loc;
  raise Error

let parse parsing_fun lexing_fun lexbuf =
  lexbuf.Lexing.lex_curr_p <-
    { lexbuf.Lexing.lex_curr_p with Lexing.pos_fname = "" };
  try
    parsing_fun lexing_fun lexbuf
  with
  | Lexer.Lexical_error(err, loc) -> lexical_error err loc
  | Parser.Error -> syntax_error (Loc(Lexing.lexeme_start lexbuf, Lexing.lexeme_end lexbuf))

let parse_implementation_file lb =
  parse Parser.implementation_file Lexer.main lb

let parse_interface_file lb =
  parse Parser.interface_file Lexer.main lb

let parse_use_file ic =
    seek_in ic 0;
    let lb = Lexing.from_channel ic in
    parse_implementation_file lb

let parse_interface ic =
    seek_in ic 0;
    let lb = Lexing.from_channel ic in
    parse_interface_file lb

(* Process one file *)

let ml_file_dependencies source_file =
  Depend.free_structure_names := Depend.StringSet.empty;
  let input_file = preprocess source_file in
  let ic = open_in_bin input_file in
  try
    let ast = parse_use_file ic in
    Depend.add_use_file Depend.StringSet.empty ast;
    if !raw_dependencies then begin
      print_raw_dependencies source_file !Depend.free_structure_names
    end else begin
      let basename = Filename.chop_extension source_file in
      let init_deps =
        if List.exists (fun ext -> Sys.file_exists (basename ^ ext)) !mli_synonyms
        then let cmi_name = basename ^ ".zci" in ([cmi_name], [cmi_name])
        else ([], []) in
      let (byt_deps, opt_deps) =
        Depend.StringSet.fold find_dependency
                              !Depend.free_structure_names init_deps in
      print_dependencies (basename ^ ".ml") byt_deps
    end;
    close_in ic; remove_preprocessed input_file
  with x ->
    close_in ic; remove_preprocessed input_file; raise x

let mli_file_dependencies source_file =
  Depend.free_structure_names := Depend.StringSet.empty;
  let input_file = preprocess source_file in
  let ic = open_in_bin input_file in
  try
    let ast = parse_interface ic in
    Depend.add_signature Depend.StringSet.empty ast;
    if !raw_dependencies then begin
      print_raw_dependencies source_file !Depend.free_structure_names
    end else begin
      let basename = Filename.chop_extension source_file in
      let (byt_deps, opt_deps) =
        Depend.StringSet.fold find_dependency
                              !Depend.free_structure_names ([], []) in
      print_dependencies (basename ^ ".zci") byt_deps
    end;
    close_in ic; remove_preprocessed input_file
  with x ->
    close_in ic; remove_preprocessed input_file; raise x

type file_kind = ML | MLI;;

let file_dependencies_as kind source_file =
  Location.input_name := source_file;
  try
    if Sys.file_exists source_file then begin
      match kind with
      | ML -> ml_file_dependencies source_file
      | MLI -> mli_file_dependencies source_file
    end
  with x ->
    let report_err = function
    | Lexer.Lexical_error (err, range) ->
        (* fprintf Format.err_formatter "@[%a%a@]@." *)
          lexical_error err range
    | Parser.Error ->
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
  if List.exists (Filename.check_suffix source_file) !ml_synonyms then
    file_dependencies_as ML source_file
  else if List.exists (Filename.check_suffix source_file) !mli_synonyms then
    file_dependencies_as MLI source_file
  else ()

(* Entry point *)

let usage = "Usage: ocamldep [options] <source files>\nOptions are:"

let print_version () =
  printf "ocamldep, version %s@." Sys.ocaml_version;
  exit 0;
;;

let print_version_num () =
  printf "%s@." Sys.ocaml_version;
  exit 0;
;;

let _ =
  add_to_load_path Filename.current_dir_name;
  Arg.parse [
     "-I", Arg.String add_to_load_path,
       "<dir>  Add <dir> to the list of include directories";
     "-impl", Arg.String (file_dependencies_as ML),
       "<f> Process <f> as a .ml file";
     "-intf", Arg.String (file_dependencies_as MLI),
       "<f> Process <f> as a .mli file";
     "-ml-synonym", Arg.String(add_to_synonym_list ml_synonyms),
       "<e> Consider <e> as a synonym of the .ml extension";
     "-mli-synonym", Arg.String(add_to_synonym_list mli_synonyms),
       "<e> Consider <e> as a synonym of the .mli extension";
     "-modules", Arg.Set raw_dependencies,
       " Print module dependencies in raw form (not suitable for make)";
     "-native", Arg.Set native_only,
       "  Generate dependencies for a pure native-code project (no .cmo files)";
     "-pp", Arg.String(fun s -> preprocessor := Some s),
       "<cmd> Pipe sources through preprocessor <cmd>";
     "-slash", Arg.Set force_slash,
       "   (Windows) Use forward slash / instead of backslash \\ in file paths";
     "-version", Arg.Unit print_version,
      " Print version and exit";
     "-vnum", Arg.Unit print_version_num,
      " Print version number and exit";
    ] file_dependencies usage;
  exit (if !error_occurred then 2 else 0)
