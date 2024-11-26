(* The Zelus compiler, version 2024-dev
  (2024-10-26-7:42) *)
open Ztypes
let m = machine(discrete) { 
          memories
            m_13 : int = 42;
            i_17 : bool = false; m_16 : int = 42; o_10 : int = 42 instances
                                                                    
          method reset  = ((i_17 <- true):unit)
          method step ((m_13:Stdlib.int)) = (():int)]}

