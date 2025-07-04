(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the sequence of source-to-source transformations applied to the *)
(* input program *)

open Misc
open Location
module Printer = Printer.Make(Typinfo) 
module Write = Write.Make(Typinfo)

let nothing p = p
let type_check _ p = Typing.program Format.std_formatter false p
    
let optim_list =
  [(* "copy", "Remove of copy variables. See below:", nothing,
   Copy.program;
   "deadcode", "Dead-code removal. See below:", nothing,
   Deadcode.program; *)
   (* "cse", "Common sub-expression elimination. See below:", nothing,
   Cse.program; *)
  (* "zopt", "Sharing of zero-crossings. See below:", nothing,
   Zopt.program *)
  ]

(* source-to-source transformations *)
let default_list =
  ["inline", "Inlining of annotated and small function calls. See below:", 
   nothing,
   Inline.program;
   "der", "Remove init and reset handlers in ODEs. See below:", nothing,
   Der.program;
   "automata", "Translation of automata. See below:", nothing,
   Automata.program;
   "present", "Translation of present. See below:", nothing,
   Present.program;
   "lastinpatterns",
   "Replace [last x] by [last* m] when [x] is pattern variable. See below:", 
   nothing,
   Lastinpatterns.program;
   "copylast",
   "Add a copy [lx = last* x] to remove false cycles. See below:", nothing,
   Copylast.program;
   "exp2eq",
   "Translate match/reset expressions in their equational form. See below:",
   nothing,
   Exp2eq.program;
   "returns",
   "Rewrite [returns (p) eq]. See below:", nothing,
   Returns.program;
   "complete", "Complete equations with [der x = 0.0]. See below:", nothing,
   Complete.program;
   "default",
   "Propagate default/initialisation into equations. See below:", nothing,
   Default.program;
   "period", "Translation of periods done. See below:", nothing,
   Period.program;
   "encore", "Add an extra step for zero-crossings on a weak transitions 
   [horizon h = 0.0]. See below:",
    nothing,
   Encore.program;
   "disc", "Translation of disc done. See below:", nothing,
   Disc.program;
   "pre", "Compilation of memories (fby/pre) into (init/last). See below:",
   nothing,
   Pre.program;
   "init", "Compilation of initializations. See below:", nothing,
   Init.program;
   "shared",
   "Normalise equations to shared variables in [x = ...]. See below:", nothing,
   Shared.program;
   "letin", "Un-nest let/in and blocks. See below:", nothing,
   Letin.program;
   (* Warning: this step does not work for the moment. The renaming *)
    (* of variables does not work. See [aform.ml] *)
    (* "aform", "A-normal form. See below:",
       (* type checks before computing A-normal form *)
       type_check,
       Aform.program; *)
   ] @ optim_list @ [
   "schedule", "Static scheduling. See below:", nothing, Schedule.program;
    "typing", "New typing step: See below:", nothing, type_check;
    "set_sorts",
   "Set the sort for variables in the environment (value/shared/state variable). 
   See below:", nothing,
   Set_sorts.program;
   ]

let number_of_passes = List.length default_list + List.length optim_list 

(* select the rewritting steps *)
module S = Set.Make (String)
let s_all =
  List.fold_left (fun acc (s, _, _, _) -> S.add s acc) S.empty default_list
let s_set = ref s_all
let step_list = ref s_all
let set_steps w =
  let set p s =
    match s with
    | "a" -> s_set := if p then s_all else S.empty
    | "inline" | "der" | "period" | "disc"
      | "lastinpatterns" | "copylast"
    | "auto" | "present"
    | "pre" | "init" | "complete" | "shared" | "encore" | "letin" 
    | "schedule" | "aform" | "deadcode" | "copy" | "exp2seq" | "default"
    | "returns" | "set_sorts" ->
       s_set := if p then S.add s !s_set else S.remove s !s_set
    | "" -> ()
    | _ -> raise (Arg.Bad ("unknown pass " ^ s)) in
  let l = String.split_on_char '+' w in
  let l_l = List.map (String.split_on_char '-') l in
  List.iter
    (fun l -> set true (List.hd l); List.iter (fun s -> set false s) (List.tl l))
    l_l
let rewrite_list () =
  List.filter (fun (w, _, _, _) -> S.mem w !s_set) default_list

(* Apply a sequence of source-to-source transformation *)
(* do equivalence checking for every step if [n_steps <> 0] *)
let main is_print print_message genv0 p n_steps =
  let compare name n_steps genv0 p p' =
  print_message is_print ("Checks the pass " ^ name ^
                            " for " ^ (string_of_int n_steps) ^" steps\n");
  let genv = Coiteration.program genv0 p in
  let genv' = Coiteration.program genv0 p' in
  Coiteration.check n_steps genv genv'; p' in
  
  let pass_number = ref 0 in

  let rewrite_and_compare genv p (name, comment, prepass, rewrite) =
    incr pass_number;
    let p = prepass p in
    let p' = rewrite genv p in
    let name_of_the_pass = "Pass " ^ name ^ " (" ^
        (string_of_int !pass_number) ^ "/" ^ (string_of_int number_of_passes)
        ^ "):\n" in
    print_message is_print (name_of_the_pass ^ comment);
    if is_print then Printer.program Format.std_formatter p';
    if n_steps = 0 then p' else compare name n_steps genv p p' in
    
  let iter genv p l = List.fold_left (rewrite_and_compare genv) p l in
  
  iter genv0 p (rewrite_list ())
