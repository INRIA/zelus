(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2022 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the main *)
open Misc
open Initial
open Compiler
   

let compile file =
  Modules.clear();
  if !no_stdlib then Initial.set_no_stdlib();
  if Filename.check_suffix file "zls"
  then
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    compile modname filename
  else if Filename.check_suffix file ".zli"
  then
    let filename = Filename.chop_suffix file ".zli" in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    interface modname filename
  else if Filename.check_suffix file ".mli"
  then
    let filename = Filename.chop_suffix file ".mli" in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    scalar_interface modname filename
  else
    raise (Arg.Bad ("don't know what to do with " ^ file))

let doc_verbose = "\tVerbose mode"
let doc_vverbose = "\t Set even more verbose mode"
and doc_version = "\t The version of the compiler"
and doc_print_types = "\t Print types"
and doc_print_causality_types = "\t Print causality types"
and doc_print_initialisation_types = "\t  Print initialization types"
and doc_nocausality = "\t (undocumented)"
and doc_noinitialisation = "\t (undocumented)"
and doc_include = "<dir> \t Add <dir> to the list of include directories"
and doc_stdlib = "<dir> \t Directory for the standard library"
and doc_locate_stdlib = "\t  Locate standard libray"
and doc_no_stdlib = "\t  Do not load the stdlib module"
and doc_typeonly = "\t  Stop after typing"
and doc_parseonly = "\t  Stop after parsing"
and doc_no_warning = "\t Turn off warnings"
let errmsg = "Options are:"

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  vverbose := true;
  set_verbose ()

let add_include d =
  load_path := d :: !load_path

let main () =
  try
    Arg.parse
      (Arg.align
         [ "-v", Arg.Unit set_verbose, doc_verbose;
           "-vv", Arg.Unit set_vverbose, doc_vverbose;
           "-version", Arg.Unit show_version, doc_version;
           "-I", Arg.String add_include, doc_include;
           "-i", Arg.Set print_types, doc_print_types;
           "-ic", Arg.Set print_causality_types, doc_print_causality_types;
           "-ii",
	   Arg.Set print_initialization_types, doc_print_initialisation_types;
           "-typeonly", Arg.Set typeonly, doc_typeonly;
           "-parseonly", Arg.Set parseonly, doc_parseonly;
           "-nocausality", Arg.Set no_causality, doc_nocausality;
           "-noinit", Arg.Set no_initialization, doc_noinitialisation;
           "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
           "-stdlib", Arg.String set_stdlib, doc_stdlib;
           "-nostdlib", Arg.Set no_stdlib, doc_no_stdlib
          ])
      compile
      errmsg
  with
  | Misc.Error | Stdlib.Exit -> exit 2
  
let _ = main ()
let _ = exit 0
 
