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

(* $Id$ *)

open Format
open Location
open Parsetree
open Misc


(* Print the dependencies *)

let load_path = ref ([] : (string * string array) list)
let force_slash = ref false
let error_occurred = ref false

(* Fix path to use '/' as directory separator instead of '\'.
   Only under Windows. *)

let fix_slash s =
  if Sys.os_type = "Unix" then s else begin
    let r = Bytes.of_string s in
    for i = 0 to Bytes.length r - 1 do
      if Bytes.get r i = '\\' then Bytes.set r i '/'
    done;
    Bytes.to_string r
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
  let uname = String.uncapitalize_ascii name in
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


let find_dependency modname acc =
  try
    let candidate = modname ^ ".zli" in
    let filename = find_file candidate in
    let basename = Filename.chop_extension filename in
    if Sys.file_exists (basename ^ ".zls")
    then (basename ^ ".zls") :: acc else (basename ^ ".zli") :: acc
  with Not_found ->
  try
    let candidate = modname ^ ".zls" in
    let filename = find_file candidate in
    let basename = Filename.chop_extension filename in
    (basename ^ ".zls") :: acc
  with Not_found ->
    acc

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
    let result = Bytes.create (String.length s + spaces) in
    let rec loop i j =
      if i >= String.length s then ()
      else if s.[i] = ' ' then begin
        Bytes.set result j '\\';
        Bytes.set result (j+1) ' ';
        loop (i+1) (j+2);
      end else begin
        Bytes.set result j (s.[i]);
        loop (i+1) (j+1);
      end
    in
    let result = Bytes.to_string result in
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


(* Optionally preprocess a source file *)

let preprocessor = ref None

exception Preprocessing_error

let preprocess sourcefile =
  match !preprocessor with
    None -> sourcefile
  | Some pp ->
      flush Stdlib.stdout;
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

let zls_dependencies source_file = 
  let input_file = preprocess source_file in
  let ic = open_in_bin input_file in
  try
    let ast = parse_use_file ic in
    let free_structure_names = Depend.source_file ast in
    close_in ic; 
    remove_preprocessed input_file;
    Depend.StringSet.fold find_dependency free_structure_names []
  with x ->
    close_in ic; 
    remove_preprocessed input_file; 
    raise x

let zli_dependencies source_file = 
  let input_file = preprocess source_file in
  let ic = open_in_bin input_file in
  try
    let ast = parse_interface ic in
    let free_structure_names = Depend.interface_file ast in
    close_in ic; 
    remove_preprocessed input_file;
    Depend.StringSet.fold find_dependency free_structure_names [] 
  with x ->
    close_in ic; 
    remove_preprocessed input_file; 
    raise x

let zls_file_dependencies source_file =
  let deps = zls_dependencies source_file in 
  print_dependencies source_file deps

let zli_file_dependencies source_file =
  let deps = zls_dependencies source_file in 
  print_dependencies source_file deps