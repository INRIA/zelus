(* The Zelus compiler, version 2024-dev
  (2024-11-26-13:35) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_35 =
{mutable time_30: 'd; mutable m_27: 'c; mutable i_33: 'b; mutable o_21: 'a}
type ('d, 'c, 'b, 'a) machine_34 =
{mutable m_24: 'd; mutable i_32: 'c; mutable m_31: 'b; mutable o_17: 'a}
let m = let machine_34  = 
          
          let machine_34_alloc _ =
            ();
            { m_24 = (42:int);
              i_32 = (false:bool); m_31 = (42:int); o_17 = (42:int) } in
          let machine_34_reset self  =
            ((self.i_32 <- true):unit) in
          let machine_34_step self ((m_24:Stdlib.int)) =
            ((self.o_17 <- (if self.i_32
                            then 0
                            else Stdlib.(+) self.m_31 self.m_24);
              self.i_32 <- false;
              self.m_31 <- Stdlib.(+) self.o_17 1; self.o_17):int) in
          Node { alloc = machine_34_alloc; reset = machine_34_reset;
                                           step = machine_34_step } in
          machine_34

let m = T_3.r_11
let m = let machine_35 (cstate_36:Ztypes.cstate) = 
          
          let machine_35_alloc _ =
            cstate_36.cmax <- Stdlib.(+) !cstate_36.cmax 1;
            { time_30 = (Obj.magic ():'e);
              m_27 = (42.:float);
              i_33 = (false:bool); o_21 = { pos = 42.; der = 0. } } in
          let machine_35_step self ((time_30:''a287), (m_27:Stdlib.float)) =
            ((let (cindex_37:Stdlib.int) = cstate_36.cindex in
              let cpos_39 = ref (!cindex_37:int) in
              cstate_36.cindex <- Stdlib.(+) !cstate_36.cindex 1;
              (if cstate_36.major
               then
                 for i_2 = !cindex_37 to 0
                 do Zls.set cstate_36.dvec !i_2 0. done
               else
                 (self.o_21.pos <- Zls.get cstate_36.cvec cpos_39;
                  cpos_39 := Stdlib.(+) cpos_39 1));
              (let (result_41:Stdlib.float) =
                   (if self.i_33 then self.o_21.pos <- self.m_27 else ());
                   self.i_33 <- false;
                   self.o_21.der <- Stdlib.(+.) 1. self.o_21.pos;
                   self.o_21.pos in
               cpos_39 := !cindex_37;
               (if cstate_36.major
                then
                  ((Zls.set cstate_36.cvec !cpos_39 self.o_21.pos;
                    cpos_39 := Stdlib.(+) cpos_39 1))
                else
                  ((Zls.set cstate_36.dvec !cpos_39 self.o_21.der;
                    cpos_39 := Stdlib.(+) cpos_39 1))); !result_41)):
            float) in
          let machine_35_reset self  =
            ((self.i_33 <- true):unit) in
          Node { alloc = machine_35_alloc; step = machine_35_step;
                                           reset = machine_35_reset } in
          machine_35

let m = T_3.r_14
