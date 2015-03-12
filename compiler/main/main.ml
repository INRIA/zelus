(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
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
  if Filename.check_suffix file ".zls"
  then 
    let filename = Filename.chop_suffix file ".zls" in
    let modname = String.capitalize(Filename.basename filename) in
    compile modname filename 
  else if Filename.check_suffix file ".zli"
  then
    let filename = Filename.chop_suffix file ".zli" in
    let modname = String.capitalize(Filename.basename filename) in
    interface modname filename
  else 
    raise (Arg.Bad ("don't know what to do with " ^ file))

let doc_verbose = " Set verbose mode"
and doc_version = " The version of the compiler"
and doc_print_types = " Print types"
and doc_print_causality = " Print causality types"
and doc_include = "<dir> Add <dir> to the list of include directories"
and doc_stdlib = "<dir> Directory for the standard library"
and doc_locate_stdlib = " Locate standard libray"
and doc_no_pervasives = " Do not load the pervasives module"
and doc_typeonly = " Stop after typing"
and doc_hybrid = " Select hybrid translation"
and doc_simulation = "<node> Simulates the node <node> \
                      and generates a file <node>.ml \n\t\t  \
                      For hybrid programs, compile with:\n\t\t  \
                bigarray.cma unix.cma -I +sundials sundials_cvode.cma zllib.cma"
and doc_sampling = "<p> Sets the sampling period to p (float <= 1.0)"
and doc_check = "<n> Check that the simulated node returns true for n steps"
and doc_use_gtk = " Use lablgtk2 interface.\n\t\t  \
                   Compile with: -I +lablgtk2 lablgtk.cma zllibgtk.cma"
and doc_inlining_level = "<n> Level of inlining"
and doc_dzero = " Turn on discrete zero-crossing detection"
and doc_nocausality = " (undocumented)"
and doc_causality = " When the flag is on, choose the old causality analysis"
and doc_noinitialisation = " (undocumented)"

let errmsg = "Options are:"

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let main () =
  try
    Arg.parse (Arg.align
      ([
        "-v", Arg.Unit set_verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-I", Arg.String add_include, doc_include;
        "-i", Arg.Set print_types, doc_print_types;
        "-ic", Arg.Set print_causality, doc_print_causality;
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
        "-noinit", Arg.Set no_initialisation, doc_noinitialisation;
        "-inline", Arg.Int set_inlining_level, doc_inlining_level;
      ]))
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

