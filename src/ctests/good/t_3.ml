(* The Zelus compiler, version 2024-dev
  (2024-11-26-13:35) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_80 =
{mutable time_71: 'd; mutable m_67: 'c; mutable i_75: 'b; mutable o_50: 'a}
type ('d, 'c, 'b, 'a) machine_79 =
{mutable time_70: 'd; mutable m_63: 'c; mutable i_74: 'b; mutable m_64: 'a}
type ('d, 'c, 'b, 'a) machine_76 =
{mutable m_53: 'd; mutable i_73: 'c; mutable m_72: 'b; mutable o_33: 'a}
let m = let machine_76  = 
          
          let machine_76_alloc _ =
            ();
            { m_53 = (42:int);
              i_73 = (false:bool); m_72 = (42:int); o_33 = (42:int) } in
          let machine_76_reset self  =
            ((self.i_73 <- true):unit) in
          let machine_76_step self ((m_53:Stdlib.int)) =
            ((self.o_33 <- (if self.i_73
                            then 0
                            else Stdlib.(+) self.m_72 self.m_53);
              self.i_73 <- false;
              self.m_72 <- Stdlib.(+) self.o_33 1; self.o_33):int) in
          Node { alloc = machine_76_alloc; reset = machine_76_reset;
                                           step = machine_76_step } in
          machine_76

let m = T_3.r_19
let m = (fun ((m_56:Stdlib.float), (m_57:Stdlib.float)) ->
          Stdlib.(+.) !m_56 !m_57)
let m = T_3.r_22
let m = (fun ((m_60:(Stdlib.float *  Stdlib.float))) ->
          let ((x_41:Stdlib.float), (y_42:Stdlib.float)) = !m_60 in
          Stdlib.(+.) !x_41 !y_42)
let m = T_3.r_24
let m = let machine_79 (cstate_81:Ztypes.cstate) = 
          
          let machine_79_alloc _ =
            cstate_81.cmax <- Stdlib.(+) !cstate_81.cmax 1;
            { time_70 = (Obj.magic ():'i);
              m_63 = (42.:float);
              i_74 = (false:bool); m_64 = { pos = 42.; der = 0. } } in
          let machine_79_step self ((time_70:''a637), (m_63:Stdlib.float)) =
            ((let (cindex_82:Stdlib.int) = cstate_81.cindex in
              let cpos_84 = ref (!cindex_82:int) in
              cstate_81.cindex <- Stdlib.(+) !cstate_81.cindex 1;
              (if cstate_81.major
               then
                 for i_2 = !cindex_82 to 0
                 do Zls.set cstate_81.dvec !i_2 0. done
               else
                 (self.m_64.pos <- Zls.get cstate_81.cvec cpos_84;
                  cpos_84 := Stdlib.(+) cpos_84 1));
              (let (result_86:Stdlib.float) =
                   (if self.i_74 then self.m_64.pos <- self.m_63 else ());
                   self.i_74 <- false;
                   self.m_64.der <- T_3.f3 (1., 2.); self.m_64.pos in
               cpos_84 := !cindex_82;
               (if cstate_81.major
                then
                  ((Zls.set cstate_81.cvec !cpos_84 self.m_64.pos;
                    cpos_84 := Stdlib.(+) cpos_84 1))
                else
                  ((Zls.set cstate_81.dvec !cpos_84 self.m_64.der;
                    cpos_84 := Stdlib.(+) cpos_84 1))); !result_86)):
            float) in
          let machine_79_reset self  =
            ((self.i_74 <- true):unit) in
          Node { alloc = machine_79_alloc; step = machine_79_step;
                                           reset = machine_79_reset } in
          machine_79

let m = T_3.r_27
let m = let machine_80 (cstate_87:Ztypes.cstate) = 
          
          let machine_80_alloc _ =
            cstate_87.cmax <- Stdlib.(+) !cstate_87.cmax 1;
            { time_71 = (Obj.magic ():'k);
              m_67 = (42.:float);
              i_75 = (false:bool); o_50 = { pos = 42.; der = 0. } } in
          let machine_80_step self ((time_71:''a651), (m_67:Stdlib.float)) =
            ((let (cindex_88:Stdlib.int) = cstate_87.cindex in
              let cpos_90 = ref (!cindex_88:int) in
              cstate_87.cindex <- Stdlib.(+) !cstate_87.cindex 1;
              (if cstate_87.major
               then
                 for i_2 = !cindex_88 to 0
                 do Zls.set cstate_87.dvec !i_2 0. done
               else
                 (self.o_50.pos <- Zls.get cstate_87.cvec cpos_90;
                  cpos_90 := Stdlib.(+) cpos_90 1));
              (let (result_92:Stdlib.float) =
                   (if self.i_75 then self.o_50.pos <- self.m_67 else ());
                   self.i_75 <- false;
                   self.o_50.der <- T_3.f3 (1., self.o_50.pos); self.o_50.pos in
               cpos_90 := !cindex_88;
               (if cstate_87.major
                then
                  ((Zls.set cstate_87.cvec !cpos_90 self.o_50.pos;
                    cpos_90 := Stdlib.(+) cpos_90 1))
                else
                  ((Zls.set cstate_87.dvec !cpos_90 self.o_50.der;
                    cpos_90 := Stdlib.(+) cpos_90 1))); !result_92)):
            float) in
          let machine_80_reset self  =
            ((self.i_75 <- true):unit) in
          Node { alloc = machine_80_alloc; step = machine_80_step;
                                           reset = machine_80_reset } in
          machine_80

let m = T_3.r_30
