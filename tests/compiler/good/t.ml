(* The Zelus compiler, version 2024-dev
  (2025-01-23-10:33) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_32 =
{mutable i_31: 'd; mutable m_24: 'c; mutable m_29: 'b; mutable m_25: 'a}
type ('b, 'a) machine_30 = {mutable m_21: 'b; mutable m_28: 'a}
let (r_9) = let (m_20:(Stdlib.int, Stdlib.int) Ztypes.node) =
                let machine_30  = 
                  
                  let machine_30_alloc _ =
                    ();{ m_21 = (42:Stdlib.int); m_28 = (42:Stdlib.int) } in
                  let machine_30_reset self  =
                    ((self.m_28 <- 0):Stdlib.unit) in
                  let machine_30_step self ((m_21:Stdlib.int)) =
                    ((self.m_28 <- self.m_21; self.m_28):Stdlib.int) in
                  Node { alloc = machine_30_alloc; reset = machine_30_reset;
                                                   step = machine_30_step } in
                  machine_30 in
            m_20
let (f) = let (m_22:(Stdlib.int, Stdlib.int) Ztypes.node) = T.r_9 in
          m_22
let (r_12) = let (m_23:(Stdlib.int, Stdlib.int) Ztypes.node) =
                 let machine_32  = 
                   let Node { alloc = i_31_alloc; step = i_31_step;
                                                  reset = i_31_reset } = T.f 
                    in
                   let machine_32_alloc _ =
                     ();
                     { m_24 = (42:Stdlib.int);
                       m_29 = (42:Stdlib.int); m_25 = (42:Stdlib.int);
                       i_31 = i_31_alloc () (* discrete *)  } in
                   let machine_32_reset self  =
                     ((self.m_29 <- 0; i_31_reset self.i_31 ):Stdlib.unit) in
                   let machine_32_step self ((m_24:Stdlib.int)) =
                     ((self.m_25 <- i_31_step self.i_31 self.m_29;
                       self.m_29 <- self.m_25; Stdlib.(+) self.m_25 self.m_24):
                     Stdlib.int) in
                   Node { alloc = machine_32_alloc; reset = machine_32_reset;
                                                    step = machine_32_step } in
                   machine_32 in
             m_23
let (g) = let (m_26:(Stdlib.int, Stdlib.int) Ztypes.node) = T.r_12 in
          m_26
