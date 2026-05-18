(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the main *)
open Misc
   
let main file =
  if Filename.check_suffix file ".zls"
  then 
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    let n_steps = !Misc.number_of_steps in
    let l_names = !Misc.main_nodes in
    Eval.main modname filename n_steps !Misc.all l_names
  else raise (Arg.Bad "Expected *.zls file.")

let doc_main = "\tThe main node to evaluate"
let doc_all = "\tEvaluate all nodes"
let doc_number_of_steps = "\tThe number of steps"
let doc_verbose = "\tVerbose mode"
let doc_vverbose = "\t Set even more verbose mode"
let doc_debug = "\t Set debug mode"
let doc_no_assert = "\tNo check of assertions"
let doc_nocausality = "\tTurn off the check that all variables are non bottom"
let doc_print_values = "\tPrint values"
let doc_total_number_of_iterations_in_fixpoints =
  "\tPrint the number of iterations in fixpoints"
let doc_esterel =
  "\tSets the interpretation of if/then/else to be constructive"
let doc_lustre =
  "\tSets the interpretation of if/then/else to be strict w.r.t any argument \n\
   \t\t(by default, it is lazy, i.e., strict w.r.t the first argument)"
let doc_static_reduction =
  "\tReduce static (compile-time) expressions"
let doc_check =
  "\tCheck equivalence at every program transformation \n\
   \t\tfor the number of steps"
and doc_inlining_level = "<n> \t Level of inlining"
and doc_inline_all = "\t Inline all function calls"

let errmsg = "Options are:"


let main () =
  try
    Arg.parse
      (Arg.align
         [ "-s", Arg.String Misc.set_main, doc_main;
           "-all", Arg.Set Misc.all, doc_all;
           "-n", Arg.Int Misc.set_number_of_steps, doc_number_of_steps;
           "-v", Arg.Unit Misc.set_verbose, doc_verbose;
           "-vv", Arg.Unit Misc.set_vverbose, doc_vverbose;
           "-debug", Arg.Unit Misc.set_debug, doc_debug;
           "-print", Arg.Set Misc.print_values, doc_print_values;
           "-noassert", Arg.Set Misc.no_assert, doc_no_assert;
           "-nocausality", Arg.Set Misc.no_causality, doc_nocausality;
           "-fix", Arg.Set Misc.compute_total_number_of_iterations_in_fixpoints,
           doc_total_number_of_iterations_in_fixpoints;
           "-esterel", Arg.Set Misc.esterel, doc_esterel;
           "-lustre", Arg.Set Misc.lustre, doc_lustre;
      ])
      main
      errmsg
  with
  | Misc.Error -> exit 2
                 
let _ = main ()
let _ = exit 0
            
