(* The Zelus compiler, version 2.2-stable
  (2022-07-11-21:34) *)
open Ztypes
let pi = 3.14159

let w = ( *. ) 2.  pi

let y0 = 4.

let y1 = 10.

let f2 ((x_46:int): int) =
  let (y_47:int) = ( * ) x_46  x_46 in
  y_47

let f3 ((x_48:int): int) =
  ( * ) x_48  x_48

type _main = unit

let main  = 
   let main_alloc _ = () in
  let main_reset self  =
    ((()):unit) in 
  let main_step self () =
    ((let ((y_51:int): int) = 3 in
      let (z_52:int) = (+) 4  y_51 in
      let _ = print_int z_52 in
      let ((y_49:int): int) = 0 in
      let (z_50:int) = (+) (-1)  y_49 in
      z_50):int) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
let x = 4

type nat = 
let x0 = 3

let x1 = 3

let x2 = 3

