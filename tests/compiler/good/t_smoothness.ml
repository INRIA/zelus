(* The Zelus compiler, version 2024-dev
  (2026-07-22-6:27) *)
open Ztypes
type ('b, 'a) machine_10 = {mutable cstate_11: 'b; mutable o_8: 'a}
let (h) =
      let h_6 =
          let machine_10 = 
            let machine_10_alloc (cstate_11) =
              cstate_11.cmax <- 1;
              { cstate_11 = (cstate_11:Ztypes.cstate);
                o_8 = { pos = (-1.); der = 0. } } in
            let machine_10_step self_9 (x_7) =
              ((let cstart_12 = self_9.cstate_11.cindex in
                let cpos_14 = ref (cstart_12:int) in
                self_9.cstate_11.cindex <- (+) self_9.cstate_11.cindex 1;
                (if self_9.cstate_11.major
                 then
                   for i_2 = cstart_12 to 0
                   do Zls.set self_9.cstate_11.dvec i_2 0. done
                 else
                   ((self_9.o_8.pos <- Zls.get self_9.cstate_11.cvec !cpos_14;
                     cpos_14 := (+) !cpos_14 1)));
                (let result_16 =
                     self_9.o_8.der <- (+.) x_7 1.; self_9.o_8.pos in
                 cpos_14 := cstart_12;
                 (if self_9.cstate_11.major
                  then
                    (((Zls.set self_9.cstate_11.cvec !cpos_14 self_9.o_8.pos;
                       cpos_14 := (+) !cpos_14 1)))
                  else
                    (((Zls.set self_9.cstate_11.dvec !cpos_14 self_9.o_8.der;
                       cpos_14 := (+) !cpos_14 1)))); result_16)):float) in
            let machine_10_reset self_9  =
              ((self_9.o_8.pos <- 0.):unit) in
             Node { alloc = machine_10_alloc;
                    step = machine_10_step; reset = machine_10_reset;
                    assertions = [] } in
          machine_10 in h_6
