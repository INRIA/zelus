open Misc
open Initial
open Compiler

let load_std_lib () =
  set_no_stdlib () ;
  interface "Stdlib" "stdlib"

let _ = load_std_lib ()
let dir_list = ["good"; "bad"]

let files dir =
  let files = Array.to_list (Sys.readdir dir) in
  let files =
    List.filter (fun file -> Filename.check_suffix file ".zlus") files in
  let files = List.sort String.compare files in
  List.map
    (fun file -> Filename.concat dir (Filename.chop_suffix file ".zlus"))
    files

let good_one file =
  let modname = String.capitalize_ascii (Filename.basename file) in
  compile modname file

exception Error

let bad_one file =
  let run () = try good_one file with _ -> raise Error in
  Alcotest.check_raises "error" Error run

let good =
  List.map (fun file -> (file, `Quick, fun () -> good_one file)) (files "good")

let bad =
  List.map (fun file -> (file, `Quick, fun () -> bad_one file)) (files "bad")

let () =
  Alcotest.run ~and_exit:false "zelus_tests" [("good", good); ("bad", bad)]
