(* The Zelus compiler, version 2024-dev
  (2024-10-26-7:42) *)
open Ztypes
let m = machine(discrete) { 
          memories
            m_23 : int = 42;
            i_31 : bool = false; m_29 : int = 42; o_16 : int = 42 instances
                                                                    
          method reset  = ((i_31 <- true):unit)
          method step ((m_23:Stdlib.int)) = (():int)]}

let m = T_3.r_10
let m = machine(discrete) { 
          memories
            m_26 : int = 42;
            i_32 : bool = false; m_30 : int = 42; o_20 : int = 42 instances
                                                                    
          method reset  = ((i_32 <- true):unit)
          method step ((m_26:Stdlib.int)) = (():int)]}

let m = T_3.r_13
