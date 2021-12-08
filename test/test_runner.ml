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

let one file =
  Format.printf "%s@." file ;
  let modname = String.capitalize_ascii (Filename.basename file) in
  compile modname file

let suite dir =
  List.map (fun file -> (file, `Quick, fun () -> one file)) (files dir)

let () =
  Alcotest.run ~and_exit:false "zelus_tests"
    (List.map (fun dir -> (dir, suite dir)) ["good"; "bad"])
