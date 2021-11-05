(* The Zelus compiler, version 2.1-dev
  (2021-05-19-23:17) *)
open Ztypes
let pi = 3.14159

let w = 6.28

let y0 = 4.

let y1 = 10.

type _main = unit

let main  = 
   let main_alloc _ = () in
  let main_reset self  =
    ((()):unit) in 
  let main_step self () =
    ((let _ = print_string "end" in
      print_newline ()):unit) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
