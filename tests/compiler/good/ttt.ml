(* The Zelus compiler, version 2024-dev
  (2025-05-13-5:25) *)
open Ztypes
type ('d, 'c, 'b, 'a) machine_11 =
{mutable time_7: 'd;
 mutable major_6: 'c; mutable init_10: 'b; mutable h_8: 'a}
let (f0) =
      let f0_4 =
          let machine_11 cstate_12 = 
            
            let machine_11_alloc _ =
              ();
              { time_7 = (-1.);
                major_6 = false; init_10 = (false:bool); h_8 = (-1.) } in
            let machine_11_step self (x_5) =
              ((self.major_6 <- !cstate_12.major;
                self.time_7 <- !cstate_12.time;
                (if !cstate_12.major then () else ());
                (let result_17 =
                     (if self.init_10
                      then self.h_8 <- (+.) self.time_7 1.
                      else ());
                     self.init_10 <- false;
                     (let z_9 = (&&) self.major_6 ((>=) self.time_7 self.h_8) in
                      self.h_8 <- (if z_9 then (+.) self.h_8 2. else self.h_8);
                      z_9) in
                 cstate_12.horizon <- min !cstate_12.horizon self.h_8;
                 (if !cstate_12.major then () else ()); result_17)):bool) in
            let machine_11_reset self  =
              ((self.init_10 <- true):unit) in
            Node { alloc = machine_11_alloc; step = machine_11_step;
                                             reset = machine_11_reset } in
            machine_11 in
      f0_4
