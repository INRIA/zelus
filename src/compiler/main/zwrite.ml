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
    let n_steps = !equivalence_checking in
    Rewrite.main modname filename n_steps 
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
let doc_number_of_fixpoint_iterations =
  "\tPrint the number of steps for fixpoints"
let doc_esterel =
  "\tSets the interpretation of if/then/else to be constructive"
let doc_lustre =
  "\tSets the interpretation of if/then/else to be strict \n\
   \t\t(that of Lustre)"
let doc_static_reduction =
  "\tReduce static (compile-time) expressions"
let doc_check =
  "<n> \t Check equivalence for that amount of steps"
and doc_inlining_level = "<n> \t Level of inlining"
and doc_inline_all = "\t Inline all function calls"
and doc_set_steps = "\t Option to control source-to-source rewriting steps\n\
    \t\t +<s> turn on step s\n\
    \t\t -<s> turn off step s\n\
    \t\t s can be: +a: takes all; -a: takes none\n\
    \t\t static: static reduction \n\
    \t\t inline: inlining \n\
    \t\t der: normalize derivative \n\
    \t\t copylast: add copy equations [lx = last* x] for lasts \n\
    \t\t lastinpatterns: add copies for lasts that are inputs or outputs \n\
    \t\t auto: remove automata statements \n\
    \t\t present: remove present statements \n\
    \t\t pre: remove pre/fby \n\
    \t\t reset: normalise resets; remove initialization (->) \n\
    \t\t complete: complete branches \n\
    \t\t encore: add an extra step when a zero-crossing \n\
    \t\t\t change a discrete-time state variable \n\
    \t\t letin: fuse blocks \n\
    \t\t schedule: static scheduling \n\
    \t\t Example: -step -a+step+inline+static. Default is +a."
let errmsg = "Options are:"


let main () =
  try
    Arg.parse
      (Arg.align
         [ "-v", Arg.Unit Misc.set_verbose, doc_verbose;
           "-vv", Arg.Unit Misc.set_vverbose, doc_vverbose;
           "-debug", Arg.Unit Misc.set_debug, doc_debug;
           "-print", Arg.Set Misc.print_values, doc_print_values;
           "-noassert", Arg.Set Misc.no_assert, doc_no_assert;
           "-nocausality", Arg.Set Misc.no_causality, doc_nocausality;
           "-fix", Arg.Set Misc.print_number_of_fixpoint_iterations,
           doc_number_of_fixpoint_iterations;
           "-esterel", Arg.Set Misc.esterel, doc_esterel;
           "-lustre", Arg.Set Misc.lustre, doc_lustre;
           "-check", Arg.Int set_equivalence_checking, doc_check;
           "-inline", Arg.Int Misc.set_inlining_level, doc_inlining_level;
           "-inlineall", Arg.Set inline_all, doc_inline_all;
           "-step", Arg.String Rewrite.set_steps, doc_set_steps;
      ])
      main
      errmsg
  with
  | Misc.Error -> exit 2
                 
let _ = main ()
let _ = exit 0
            
