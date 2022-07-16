(* The Zelus compiler, version 2.2-stable
  (2022-07-14-3:57) *)
open Ztypes
let x = 10

type ('b , 'a) _main =
  { mutable m_14 : 'b ; mutable m_12 : 'a }

let main  = 
   let main_alloc _ =
     ();{ m_14 = (42:int) ; m_12 = (42:int) } in
  let main_reset self  =
    ((self.m_12 <- 1 ; self.m_14 <- 0):unit) in 
  let main_step self () =
    ((let (x_13:int) = self.m_12 in
      let (x_15:int) = self.m_14 in
      let ((x_11:int): int) = x_15 in
      self.m_12 <- x_11 ; self.m_14 <- (+) x_11  x_13 ; x_11):int) in
  Node { alloc = main_alloc; reset = main_reset ; step = main_step }
