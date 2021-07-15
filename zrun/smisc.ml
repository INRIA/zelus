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

let main_node = ref (None: string option)
let set_main s = main_node := Some(s)

let set_check = ref false
              
let number_of_steps = ref 0
let set_number_of_steps n = number_of_steps := n

let number_of_fixpoint_iterations = ref 0
let print_number_of_fixpoint_iterations = ref false
let incr_number_of_fixpoint_iterations n =
  number_of_fixpoint_iterations := !number_of_fixpoint_iterations + n
let reset_number_of_fixpoint_iterations () = number_of_fixpoint_iterations := 0
                    
let no_assert = ref false

let set_verbose = ref false

let set_nocausality = ref false
