(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the main *)
open Smisc
   
let main file =
  if Filename.check_suffix file ".zls"
  then 
    let filename = Filename.chop_extension file in
    let modname = String.capitalize_ascii (Filename.basename filename) in
    let n_steps = !Smisc.number_of_steps in
    let l_nodes = !Smisc.main_nodes in
    if !Smisc.all then
      Eval.all modname filename n_steps 
    else
      Eval.main modname filename n_steps l_nodes
  else raise (Arg.Bad "Expected *.zls file.")

let doc_main = "\tThe main node to evaluate"
let doc_all = "\tEvaluate all nodes"
let doc_number_of_steps = "\tThe number of steps"
let doc_verbose = "\tVerbose mode"
let doc_vverbose = "\t Set even more verbose mode"
let doc_no_assert = "\tNo check of assertions"
let doc_nocausality = "\tTurn off the check that are variables are non bottom"
let doc_print_values = "\tPrint values"
let doc_number_of_fixpoint_iterations =
  "\tPrint the number of steps for fixpoints"
let doc_esterel =
  "\t Sets the interpretation of if/then/else to that of Esterel"
let doc_lustre =
  "\t Sets the interpretation of if/then/else to that of Lustre"
                   
let errmsg = "Options are:"


let main () =
  try
    Arg.parse
      (Arg.align
         [ "-s", Arg.String Smisc.set_main, doc_main;
           "-all", Arg.Set Smisc.all, doc_all;
           "-n", Arg.Int Smisc.set_number_of_steps, doc_number_of_steps;
           "-v", Arg.Unit set_verbose, doc_verbose;
           "-vv", Arg.Unit set_vverbose, doc_vverbose;
           "-iv", Arg.Set print_values, doc_print_values;
           "-noassert", Arg.Set Smisc.no_assert, doc_no_assert;
           "-nocausality", Arg.Set Smisc.set_nocausality, doc_nocausality;
           "-fix", Arg.Set Smisc.print_number_of_fixpoint_iterations,
           doc_number_of_fixpoint_iterations;
           "-esterel", Arg.Set Smisc.set_esterel, doc_esterel;
           "-lustre", Arg.Set Smisc.set_lustre, doc_lustre
      ])
      main
      errmsg
  with
  | _ -> exit 2
                 
let _ = main ()
let _ = exit 0
            
