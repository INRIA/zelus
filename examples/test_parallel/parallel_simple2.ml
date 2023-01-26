(* The Zelus compiler, version 2.2-dev
  (2023-01-19-17:40) *)
open Ztypes
type _exec = unit

let exec  = 
   let exec_alloc _ = () in
  let exec_reset self  =
    ((()):unit) in  let exec_step self () =
                      (():unit) in
  Node { alloc = exec_alloc; reset = exec_reset ; step = exec_step }
