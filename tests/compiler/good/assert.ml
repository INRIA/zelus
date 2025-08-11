(* The Zelus compiler, version 2024-dev
  (2025-05-13-5:25) *)
open Ztypes
type ('a) machine_14 = {mutable x_7: 'a}
let (g) =
      let g_6 =
          let machine_14 cstate_15 = 
            
            let machine_14_alloc _ =
              cstate_15.cmax <- (+) cstate_15.cmax 1;
              { x_7 = { pos = (-1.); der = 0. } } in
            let machine_14_step self _ =
              ((let cindex_16 = cstate_15.cindex in
                let cpos_18 = ref (cindex_16:int) in
                cstate_15.cindex <- (+) cstate_15.cindex 1;
                (if cstate_15.major
                 then
                   for i_2 = cindex_16 to 0
                   do Zls.set cstate_15.dvec i_2 0. done
                 else
                   ((self_9.x_7.pos <- Zls.get cstate_15.cvec !cpos_18;
                     cpos_18 := (+) !cpos_18 1)));
                (let result_20 =
                     self_9.x_7.der <- 1.;
                     (let _ = () in
                      let _ = () in
                      self_9.x_7.pos) in
                 cpos_18 := cindex_16;
                 (if cstate_15.major
                  then
                    (((Zls.set cstate_15.cvec !cpos_18 self_9.x_7.pos;
                       cpos_18 := (+) !cpos_18 1)))
                  else
                    (((Zls.set cstate_15.dvec !cpos_18 self_9.x_7.der;
                       cpos_18 := (+) !cpos_18 1)))); result_20)):float) in
            let machine_14_reset self  =
              ((self_9.x_7.pos <- 0.):unit) in
            Node { alloc = machine_14_alloc; step = machine_14_step;
                                             reset = machine_14_reset } in
            machine_14 in
      g_6
