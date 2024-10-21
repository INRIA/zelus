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

(* useful stuff *)

let header_in_file =
  let open Config in
  "The Zelus compiler, version " ^ version ^ "-" ^subversion ^ "\n\  (" ^ date ^ ")"

(* error during the whole process *)
exception Error
        
let name_of_stdlib_module = "Stdlib"

let standard_lib = Config.stdlib

(* list of modules initially opened *)
let default_used_modules = ref [name_of_stdlib_module]

(* load paths *)
let load_path = ref ([standard_lib])

let set_stdlib p =
  load_path := [p]

(* where is the standard library *)
let locate_stdlib () =
  Printf.printf "%s\n" standard_lib

let show_version () =
  let open Config in
  Printf.printf "The ZRun Interpreter, version %s-%s (%s)\n"
    version subversion date;
  Printf.printf "Std lib: "; locate_stdlib ();
  Printf.printf "\n";
  ()


(* sets the main simulation node *)
let simulation_node = ref None
let set_simulation_node (n:string) = simulation_node := Some(n)

(* sets the output filepath *)
let outname = ref None
let set_outname (n:string) = outname := Some(n)

(* sets the output filepath for nodes *)
let node_outname = ref None
let set_node_outname (n:string) = node_outname := Some(n)

(* sets the checking flag *)
let number_of_checks = ref 0
let set_check (n: int) = number_of_checks := n

(* sampling the main loop on a real timer *)
let sampling_period = ref 0.0
let set_sampling_period p = sampling_period := p

(* level of inlining *)
let inlining_level = ref 10
let set_inlining_level l = inlining_level := l
let inline_all = ref false

let verbose = ref false
let vverbose = ref false
let debug = ref false

let set_verbose () =
  verbose := true;
  Printexc.record_backtrace true

let set_vverbose () =
  vverbose := true;
  set_verbose ()

let set_debug () =
  debug := true;
  set_verbose ()

let print_types = ref false
let no_stdlib = ref false
let no_warning = ref false
let print_causality_types = ref false
let no_simplify_causality_types = ref false
let print_initialization_types = ref false
let no_causality = ref false
let no_initialization = ref false
let typeonly = ref false
let parseonly = ref false
let use_gtk = ref false
let zsign = ref false
let with_copy = ref false
let use_rif = ref false

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
let reset_number_of_fixpoint_iterations () = 
  number_of_fixpoint_iterations := 0
                    
(* remove the check of assertions during evaluation *)
let no_assert = ref false

(* remove the check that fix-point equation produce non bottom values *)
let no_causality = ref false

(* sets the interpretation of the if/then/else to Esterel *)
let esterel = ref false

(* sets the interpretation of the if/then/else to Lustre *)
let lustre = ref false

(* static reduction *)
let static_reduction = ref false

(* check equivalence *)
let equivalence_checking = ref 0
let set_equivalence_checking n = equivalence_checking := n

(* sets the inline flags *)
let inlining_level = ref 10
let set_inlining_level l = inlining_level := l
let inline_all = ref false

(* generic and non generic variables in the various type systems *)
let generic = -1
let notgeneric = 0
let maxlevel = max_int

let binding_level = ref 0
let top_binding_level () = !binding_level = 0

let push_binding_level () = binding_level := !binding_level + 1
let pop_binding_level () =
  binding_level := !binding_level - 1;
  assert (!binding_level > generic)
let reset_binding_level () = binding_level := 0

(* Internal error in the compiler. *)
let internal_error message printer input =
  Format.eprintf "@[Internal error (%s)@. %a@.@]" message printer input;
  raise Error

(* Not yet implemented *)
let not_yet_implemented message =
  Format.eprintf "@[Not yet implemented (%s)@.@]" message;
  raise Error
