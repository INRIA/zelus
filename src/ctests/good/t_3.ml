(* The Zelus compiler, version 2024-dev
  (2024-10-30-16:57) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_13 =
{mutable m_9: 'd; mutable i_12: 'c; mutable m_11: 'b; mutable o_7: 'a}
let m = let machine_13  = 
          
          let machine_13_alloc _ =
            ();
            { m_9 = (42:int);
              i_12 = (false:bool); m_11 = (42:int); o_7 = (42:int) } in
          let machine_13_reset self  =
            ((self.i_12 <- true):unit) in
          let machine_13_step self ((m_9:Stdlib.int)) =
            ((self.o_7 <- (if self.i_12
                           then 0
                           else Stdlib.(+) self.m_11 self.m_9);
              self.i_12 <- false;
              self.m_11 <- Stdlib.(+) self.o_7 1; self.o_7):int) in
          Node { alloc = machine_13_alloc; reset = machine_13_reset;
                                           step = machine_13_step } in
          machine_13

