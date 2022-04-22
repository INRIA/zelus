open Zmisc
open Initial
open Compiler

(* List file names that match a given extension [ext] in the directory [dir]. *)
let files dir ext =
  Array.to_list (Sys.readdir dir)
  |> List.filter (fun file -> Filename.check_suffix file ext)
  |> List.sort String.compare
  |> List.map (fun file -> Filename.concat dir (Filename.chop_suffix file ext))

(* Compile and load Stdlib. *)
let _ =
  set_no_stdlib () ;
  interface "Stdlib" "stdlib" ;
  default_used_modules := ["Stdlib"]

(* Compile one file. *)
let good_one file =
  Modules.clear () ;
  let modname = String.capitalize_ascii (Filename.basename file) in
  compile modname file

exception Error

(* Compile one bad file and check that an exception is raised. *)
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
let () = Alcotest.run  "zelus_tests" [("good", good); ("bad", bad)]
