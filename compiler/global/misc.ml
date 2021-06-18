(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
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

let set_verbose = ref false

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
