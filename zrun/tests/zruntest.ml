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

open Misc
open Initial
open Compiler

(* List file names that match a given extension [ext] in the directory [dir]. *)
let files dir ext =
  Array.to_list (Sys.readdir dir)
  |> List.filter (fun file -> Filename.check_suffix file ext)
  |> List.sort String.compare
  |> List.map (fun file -> Filename.concat dir (Filename.chop_suffix file ext))

(* Compile and load Stdlib. *)
(*
let _ =
  Initial.set_no_stdlib ();
  (* interface "Stdlib" "stdlib" ; *)
   default_used_modules := ["Stdlib"]
 *)

let n_steps = 10
let is_check = false

(* Run one file. *)
let good_one filename =
  Modules.clear ();
  let modname = String.capitalize_ascii (Filename.basename filename) in
  Eval.main modname filename n_steps is_check ["main"]

exception Error

(* Run one bad file and check that an exception is raised. *)
let bad_one file =
  let run () = try good_one file with _ -> raise Error in
  Alcotest.check_raises "error" Error run

(* Check all good files. *)
let good =
  load_path := "./good" :: !load_path ;
  List.map
    (fun file -> (file, `Quick, fun () -> good_one file))
    (files "good" ".zls")

(* Check all bad files. *)
let bad =
  load_path := "./bad" :: !load_path ;
  List.map
    (fun file -> (file, `Quick, fun () -> bad_one file))
    (files "bad" ".zls")


(* Main test runner. *)
let () = Alcotest.run  "zrun_tests" [("good", good); ("bad", bad)]
