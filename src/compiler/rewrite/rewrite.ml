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

(* the sequence of source-to-source transformations applied to the input program *)
open Misc
open Location
               

let optim_list =
  ["aform", "A-normal form. See below:",
   Aform.program;
   "deadcode", "Dead-code removal. See below:",
   Deadcode.program;
   (* "cse", "Common sub-expression elimination. See below:",
   Cse.program; *)
  "copy", "Remove of copy variables. See below:",
   Copy.program;
   (* "zopt", "Sharing of zero-crossings. See below:",
   Zopt.program *)
  ]

let default_list =
  ["static", "Static reduction done. See below:",
   Static.program;
   "inline", "Inlining done. See below:",
   Inline.program;
   "automata", "Translation of automata. See below:",
   Automata.program;
   "present", "Translation of present. See below:",
   Present.program;
   "lastinpatterns",
   "Replace [last x] by [last* m] when [x] is an input variable. See below:",
   Lastinpatterns.program;
   "copylast",
   "Add a copy [lx = last* x] to remore false cycles when [x] \n\
    is a local variable. See below:",
   Copylast.program;
   "der", "Remove initialisation and reset handlers in definitions of derivatives.\
           See below:",
   Der.program;
   "exp2eq",
   "translate match and reset expressions in their equational form. See below:",
   Exp2eq.program;
   "returns",
   "Rewrite [returns (p) eq]. See below:",
   Returns.program;
   "complete", "Complete equations with [der x = 0.0]. See below:",
   Complete.program;
   "default",
   "Translate locals into let/rec (propagate default/initialisation).\
    See below:",
   Default.program;
   "pre", "Compilation of memories (fby/pre) into (init/last). See below:",
   Pre.program;
   "period", "Translation of periods done. See below:",
   Period.program;
   "encore", "Add horizons [horizon h = 0.0] for zero-crossings. See below:",
   Encore.program;
   "disc", "Translation of disc done. See below:",
   Disc.program;
   "reset", "Compilation of initialization and resets. See below:",
   Reset.program;
   "shared",
   "Normalise equations to shared variables in [x = ...]. See below:",
   Shared.program;
   "letin", "Un-nesting of let/in and blocks. See below:",
   Letin.program] @ optim_list @ [
   "schedule", "Static scheduling. See below:",
   Schedule.program ]

(* select the rewritting steps *)
module S = Set.Make (String)
let s_all = List.fold_left (fun acc (s, _, _) -> S.add s acc) S.empty default_list
let s_set = ref s_all
let step_list = ref s_all
let set_steps w =
  let set p s =
    match s with
    | "a" -> s_set := if p then s_all else S.empty
    | "static" | "inline" | "der" | "period" | "disc"
      | "lastinpatterns" | "copylast"
    | "auto" | "present"
    | "pre" | "reset" | "complete" | "shared" | "encore" | "letin" 
    | "schedule" | "aform" | "deadcode" | "copy" | "exp2seq" | "default"
    | "returns" ->
       s_set := if p then S.add s !s_set else S.remove s !s_set
    | "" -> ()
    | _ -> raise (Arg.Bad ("unknown pass " ^ s)) in
  let l = String.split_on_char '+' w in
  let l_l = List.map (String.split_on_char '-') l in
  List.iter
    (fun l -> set true (List.hd l); List.iter (fun s -> set false s) (List.tl l))
    l_l
let rewrite_list () =
  List.filter (fun (w, _, _) -> S.mem w !s_set) default_list

(* Apply a sequence of source-to-source transformation *)
(* do equivalence checking for every step if [n_steps <> 0] *)
let main print_message genv0 p n_steps =
  let compare name n_steps genv0 p p' =
  print_message ("Checks the pass " ^ name ^
                   " for " ^ (string_of_int n_steps) ^" steps\n");
  let genv = Coiteration.program genv0 p in
  let genv' = Coiteration.program genv0 p' in
  Coiteration.check n_steps genv genv'; p' in
  
  let rewrite_and_compare genv p (name, comment, rewrite) =
    let p' = rewrite genv p in
    print_message comment;
    if !Misc.verbose then Printer.program Format.err_formatter p';
    if n_steps = 0 then p' else compare name n_steps genv p p' in
    
  let iter genv p l = List.fold_left (rewrite_and_compare genv) p l in
  
  iter genv0 p (rewrite_list ())
