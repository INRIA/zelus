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

open Misc

exception Error
        
let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  vverbose := true;
  set_verbose ()

(* the list of nodes to evaluate *)
let main_nodes = ref ([] :string list)
let set_main s = main_nodes := s :: !main_nodes

(* evaluate all nodes *)
let all = ref false
                
let print_values = ref false
                 
(* number of synchronous steps for the evaluation *)
let number_of_steps = ref 0
let set_number_of_steps n = number_of_steps := n

let number_of_fixpoint_iterations = ref 0
let print_number_of_fixpoint_iterations = ref false
let incr_number_of_fixpoint_iterations n =
  number_of_fixpoint_iterations := !number_of_fixpoint_iterations + n
let reset_number_of_fixpoint_iterations () = number_of_fixpoint_iterations := 0
                    
(* remove the check of assertions during evaluation *)
let no_assert = ref false

(* remove the check that fix-point equation produce non bottom values *)
let set_nocausality = ref false

(* sets the interpretation of the if/then/else to Esterel *)
let set_esterel = ref false

(* sets the interpretation of the if/then/else to Lustre *)
let set_lustre = ref false
