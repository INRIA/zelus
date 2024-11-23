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

(* the main *)
open Misc
open Compiler

let compile file =
  Modules.clear();
  if !Misc.no_stdlib then Initial.set_no_stdlib();
  if Filename.check_suffix file ".zls" || Filename.check_suffix file ".zlus"
  then
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    Compiler.compile modname filename
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

let doc_verbose = "\t Set verbose mode"
let doc_vverbose = "\t Set even more verbose mode"
and doc_version = "\t The version of the compiler"
and doc_outname = "<name> \t Simulation file name <name>"
and doc_print_types = "\t Print types"
and doc_print_causality_types = "\t Print causality types"
and doc_print_initialization_types = "\t  Print initialization types"
and doc_include = "<dir> \t Add <dir> to the list of include directories"
and doc_stdlib = "<dir> \t Directory for the standard library"
and doc_locate_stdlib = "\t  Locate standard libray"
and doc_no_stdlib = "\t  Do not load the stdlib module"
and doc_no_zlstdlib = "\t  Do not load the zlstdlib module"
and doc_parseonly = "\t  Stop after parsing"
and doc_typeonly = "\t  Stop after typing"
and doc_rewriteonly = "\t  Stop after rewritting"
and doc_hybrid = "\t  Select hybrid translation"
and doc_simulation =
  "<node> \t Simulates the node <node> and generates a file <out>.ml\n\
   \t\t   where <out> is equal to the argument of -o if the flag\n\
   \t\t   has been set, or <node> otherwise"
and doc_sampling = "<p> \t Sets the sampling period to p (float <= 1.0)"
and doc_use_gtk = "\t Use lablgtk2 interface."
and doc_inlining_level = "<n> \t Level of inlining"
and doc_inline_all = "\t Inline all function calls"
and doc_dzero = "\t Turn on discrete zero-crossing detection"
and doc_nocausality = "\t (undocumented)"
and doc_no_initialization = "\t (undocumented)"
and doc_nosimplify = "\t (undocumented)"
and doc_no_deadcode = "\t (undocumented)"
and doc_zsign = "\t Use the sign function for the zero-crossing argument"
and doc_with_copy = "\t Add of a copy method for the state"
and doc_no_opt = "\t (undocumented)"
and doc_no_warning = "\t Turn off warnings"
and doc_check = "<n> \t Check equivalence for that amount of steps"
and doc_set_steps = "\t Option to control source-to-source rewriting steps\n\
    \t\t +<s> turn on step s\n\
    \t\t -<s> turn off step s\n\
    \t\t s can be: +a: takes all; -a: takes none\n\
    \t\t static: static reduction \n\
    \t\t inline: inlining \n\
    \t\t der: normalize derivative \n\
    \t\t period: remove periods \n\
    \t\t disc: remove discrete zero-crossings \n\
    \t\t copylast: add copy equations [lx = last* x] for lasts \n\
    \t\t lastinpatterns: add copies for lasts that are inputs or outputs \n\
    \t\t auto: remove automata statements \n\
    \t\t present: remove present statements \n\
    \t\t exp2eq: remove pattern matching and resets on expressions \n\
    \t\t returns: remove [returns (p) eq] \n\
    \t\t pre: remove pre/fby \n\
    \t\t init: remove initialization (->) \n\
    \t\t complete: complete branches \n\
    \t\t encore: add an extra step when a zero-crossing \n\
    \t\t\t change a discrete-time state variable \n\
    \t\t letin: fuse blocks \n\
    \t\t schedule: static scheduling \n\
    \t\t aform: translation into A-normal form \n\
    \t\t copy: remove copy variables \n\
    \t\t Example: -step -a+step+inline+static. Default is +a."
let errmsg = "Options are:"

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  vverbose := true;
  set_verbose ()

let add_include d =
  load_path := d :: !load_path

let set_gtk () =
    use_gtk := true;
    match !load_path with
    | [stdlib] -> add_include (stdlib ^ "-gtk")
    | _ -> ()

let main () =
  try
    Arg.parse
      (Arg.align [
          "-v", Arg.Unit set_verbose, doc_verbose;
          "-vv", Arg.Unit set_vverbose, doc_vverbose;
          "-version", Arg.Unit show_version, doc_version;
          "-I", Arg.String add_include, doc_include;
          "-i", Arg.Set print_types, doc_print_types;
          "-ic", Arg.Set print_causality_types, doc_print_causality_types;
          "-ii", Arg.Set print_initialization_types, doc_print_initialization_types;
          "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
          "-stdlib", Arg.String set_stdlib, doc_stdlib;
          "-nostdlib", Arg.Set no_stdlib, doc_no_stdlib;
          "-parseonly", Arg.Set parseonly, doc_parseonly;
          "-typeonly", Arg.Set typeonly, doc_typeonly;
          "-rewriteonly", Arg.Set rewriteonly, doc_rewriteonly;
          "-s", Arg.String set_simulation_node, doc_simulation;
          "-sampling", Arg.Float set_sampling_period, doc_sampling;
          "-gtk2", Arg.Unit set_gtk, doc_use_gtk;
          "-nocausality", Arg.Set no_causality, doc_nocausality;
          "-noinit", Arg.Set no_initialization, doc_no_initialization;
          "-inline", Arg.Int set_inlining_level, doc_inlining_level;
          "-inlineall", Arg.Set inline_all, doc_inline_all;
          "-zsign", Arg.Set zsign, doc_zsign;
          "-copy", Arg.Set with_copy, doc_with_copy;
          "-check", Arg.Int set_check_equivalence_for_n_steps, doc_check;
          "-step", Arg.String Rewrite.set_steps, doc_set_steps;
      ])
      compile
      errmsg;
    begin
      match !simulation_node with
      | Some(name) ->
          Simulator.main !outname name !sampling_period !number_of_checks !use_gtk
      | _ -> ()
    end
  with
  | Error -> exit 2;;

main ();;
exit 0;;
