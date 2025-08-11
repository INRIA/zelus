(* The Zelus compiler, version 2024-dev
  (2025-05-13-5:25) *)
open Ztypes
type ('a) machine_11 = {mutable x_6: 'a}
let (g) =
      let g_5 =
          let machine_11 cstate_12 = 
            
            let machine_11_alloc _ =
              cstate_12.cmax <- (+) cstate_12.cmax 1;
              { x_6 = { pos = (-1.); der = 0. } } in
            let machine_11_step self _ =
              ((let cindex_13 = cstate_12.cindex in
                let cpos_15 = ref (cindex_13:int) in
                cstate_12.cindex <- (+) cstate_12.cindex 1;
                (if cstate_12.major
                 then
                   for i_1 = cindex_13 to 0
                   do Zls.set cstate_12.dvec i_1 0. done
                 else
                   ((self_8.x_6.pos <- Zls.get cstate_12.cvec !cpos_15;
                     cpos_15 := (+) !cpos_15 1)));
                (let result_17 =
                     self_8.x_6.der <- 1.; (let _ = () in
                                            self_8.x_6.pos) in
                 cpos_15 := cindex_13;
                 (if cstate_12.major
                  then
                    (((Zls.set cstate_12.cvec !cpos_15 self_8.x_6.pos;
                       cpos_15 := (+) !cpos_15 1)))
                  else
                    (((Zls.set cstate_12.dvec !cpos_15 self_8.x_6.der;
                       cpos_15 := (+) !cpos_15 1)))); result_17)):float) in
            let machine_11_reset self  =
              ((self_8.x_6.pos <- 0.):unit) in
            Node { alloc = machine_11_alloc; step = machine_11_step;
                                             reset = machine_11_reset } in
            machine_11 in
      g_5
