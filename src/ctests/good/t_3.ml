(* The Zelus compiler, version 2024-dev
  (2024-11-26-13:35) *)
open Ztypes
let m = type ('d, 'c, 'b, 'a) _self =
          { mutable m_13 : 'd;
            mutable i_17 : 'c; mutable m_16 : 'b; mutable o_10 : 'a }

let self  = 
  
  let self_alloc _ =
    ();
    { m_13 = (42:int); i_17 = (false:bool); m_16 = (42:int); o_10 = (42:int) } in
  let self_reset self  =
    ((self.i_17 <- true):unit) in
  let self_step self ((m_13:Stdlib.int)) =
    ((self.o_10 <- (if i_17 then 0 else Stdlib.(+) m_16 m_13);
      self.i_17 <- false; self.m_16 <- Stdlib.(+) o_10 1; self.o_10):
    int) in
  Node { alloc = self_alloc; reset = self_reset; step = self_step }

let m = T_3.r_7
