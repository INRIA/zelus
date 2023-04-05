(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2023 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* useful stuff *)

(* error during the whole process *)
exception Error

let header_in_file =
  let open Config in
  "The Zelus compiler, version "
  ^ version ^ "-" ^subversion ^ "\n\  (" ^ date ^ ")"

(* standard module *)
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
  Printf.printf "The Zelus compiler, version %s-%s (%s)\n"
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

(* turn on the discrete zero-crossing detection *)
let dzero = ref false

(* other options of the compiler *)
let verbose = ref false
let vverbose = ref false
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
