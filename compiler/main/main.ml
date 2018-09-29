(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2018                                               *)
(*                                                                        *)
(*  Marc Pouzet  Timothy Bourke                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* the main *)
open Misc
open Initial
open Compiler

let compile file =
  if Filename.check_suffix file ".zls" || Filename.check_suffix file ".zlus"
  then 
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii(Filename.basename filename) in
    compile modname filename 
  else if Filename.check_suffix file ".zli"
  then
    let filename = Filename.chop_suffix file ".zli" in
    let modname = String.capitalize_ascii(Filename.basename filename) in
    interface modname filename
  else 
    raise (Arg.Bad ("don't know what to do with " ^ file))

let doc_verbose = "\t Set verbose mode"
and doc_version = "\t The version of the compiler"
and doc_print_types = "\t Print types"
and doc_print_causality_types = "\t Print causality types"
and doc_print_initialization_types = "\t  Print initialization types"
and doc_include = "<dir> \t Add <dir> to the list of include directories"
and doc_stdlib = "<dir> \t Directory for the standard library"
and doc_locate_stdlib = "\t  Locate standard libray"
and doc_no_pervasives = "\t  Do not load the pervasives module"
and doc_typeonly = "\t  Stop after typing"
and doc_hybrid = "\t  Select hybrid translation"
and doc_simulation =
  "<node> \t Simulates the node <node> and generates a file <node>.ml \n\
          \t           For hybrid programs, compile with:\n\
          \t           bigarray.cma unix.cma -I +sundials sundials_cvode.cma zllib.cma"
and doc_sampling = "<p> \t Sets the sampling period to p (float <= 1.0)"
and doc_check = "<n> \t Check that the simulated node returns true for n steps"
and doc_use_gtk = "\t Use lablgtk2 interface.\n\
                   \t           Compile with: -I +lablgtk2 lablgtk.cma zllibgtk.cma"
and doc_inlining_level = "<n> \t  Level of inlining"
and doc_dzero = "\t  Turn on discrete zero-crossing detection"
and doc_nocausality = "\t  (undocumented)"
and doc_no_opt = "\t  (undocumented)"
and doc_no_deadcode = "\t  (undocumented)"
and doc_noinitialisation = "\t  (undocumented)"
and doc_nosimplify = "\t  (undocumented)"
and doc_noreduce = "\t  (undocumented)"
and doc_lmm = "<n>\t  Translate the node into Lustre--"
and doc_red_name = "\t  Static reduction for"
and doc_all =
  "\t  Compile all functions (including those with static parameters)"
let errmsg = "Options are:"

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let main () =
  try
    Arg.parse (Arg.align
      [
        "-v", Arg.Unit set_verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-I", Arg.String add_include, doc_include;
        "-i", Arg.Set print_types, doc_print_types;
        "-ic", Arg.Set print_causality_types, doc_print_causality_types;
        "-ii",
	Arg.Set print_initialization_types, doc_print_initialization_types;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-typeonly", Arg.Set typeonly, doc_typeonly;
        "-s", Arg.String set_simulation_node, doc_simulation;
        "-sampling", Arg.Float set_sampling_period, doc_sampling;
        "-check", Arg.Int set_check, doc_check;
        "-gtk2", Arg.Set use_gtk, doc_use_gtk;
        "-dzero", Arg.Set dzero, doc_dzero;
        "-nocausality", Arg.Set no_causality, doc_nocausality;
        "-nopt", Arg.Set no_opt, doc_no_opt;
        "-nodeadcode", Arg.Set no_deadcode, doc_no_deadcode;
        "-noinit", Arg.Set no_initialisation, doc_noinitialisation;
        "-inline", Arg.Int set_inlining_level, doc_inlining_level;
	"-nosimplify", Arg.Set no_simplify_causality_type, doc_nosimplify;
        "-noreduce", Arg.Set no_reduce, doc_noreduce;
        "-lmm", Arg.String set_lmm_nodes, doc_lmm;
	"-all", Arg.Set all, doc_all;
        
      ])
      compile
      errmsg;
    begin
      match !simulation_node with
        | Some(name) -> 
	    Simulator.main name !sampling_period !number_of_checks !use_gtk
        | _ -> ()
    end
  with
  | Misc.Error -> exit 2;;

main ();;
exit 0;;

