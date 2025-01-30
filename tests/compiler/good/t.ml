(* The Zelus compiler, version 2024-dev
  (2025-01-23-10:33) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_32 =
{mutable i_31: 'd; mutable m_24: 'c; mutable m_29: 'b; mutable m_25: 'a}
type ('b, 'a) machine_30 = {mutable m_21: 'b; mutable m_28: 'a}
let m = let machine_30  = 
          
          let machine_30_alloc _ =
            ();{ m_21 = (42:int); m_28 = (42:int) } in
          let machine_30_reset self  =
            ((self.m_28 <- 0):unit) in
          let machine_30_step self ((m_21:Stdlib.int)) =
            ((self.m_28 <- self.m_21; self.m_28):int) in
          Node { alloc = machine_30_alloc; reset = machine_30_reset;
                                           step = machine_30_step } in
          machine_30

let m = T.r_9
