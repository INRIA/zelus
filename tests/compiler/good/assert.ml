(* The Zelus compiler, version 2024-dev
  (2025-05-13-5:25) *)
open Ztypes
type ('a) machine_16 = {mutable x_11: 'a}
let (g) =
      let (g_8:'c * 'd -C-> float) =
          let machine_16 (cstate_23:Ztypes.cstate) = 
            
            let machine_16_alloc _ =
              cstate_23.cmax <- (+) cstate_23.cmax 1;
              { x_11 = { pos = (-1.); der = 0. } } in
            let machine_16_step self_13 ((x1_9:'c), (x2_10:'d)) =
              ((let (cindex_24:int) = cstate_23.cindex in
                let cpos_26 = ref (cindex_24:int) in
                cstate_23.cindex <- (+) cstate_23.cindex 1;
                (if cstate_23.major
                 then
                   for i_2 = cindex_24 to 0
                   do Zls.set cstate_23.dvec i_2 0. done
                 else
                   ((self_13.x_11.pos <- Zls.get cstate_23.cvec !cpos_26;
                     cpos_26 := (+) !cpos_26 1)));
                (let (result_28:float) =
                     self_13.x_11.der <- 1.; (let _ = () in
                                              self_13.x_11.pos) in
                 cpos_26 := cindex_24;
                 (if cstate_23.major
                  then
                    (((Zls.set cstate_23.cvec !cpos_26 self_13.x_11.pos;
                       cpos_26 := (+) !cpos_26 1)))
                  else
                    (((Zls.set cstate_23.dvec !cpos_26 self_13.x_11.der;
                       cpos_26 := (+) !cpos_26 1)))); result_28)):float) in
            let machine_16_reset self_13  =
              ((self_13.x_11.pos <- 0.):unit) in
            let machine_15 (cstate_17:Ztypes.cstate) = 
              
              let machine_15_alloc _ =
                cstate_17.cmax <- (+) cstate_17.cmax 1;
                { y_12 = { pos = (-1.); der = 0. } } in
              let machine_15_step self_14 self_13 =
                ((let (cindex_18:int) = cstate_17.cindex in
                  let cpos_20 = ref (cindex_18:int) in
                  cstate_17.cindex <- (+) cstate_17.cindex 1;
                  (if cstate_17.major
                   then
                     for i_2 = cindex_18 to 0
                     do Zls.set cstate_17.dvec i_2 0. done
                   else
                     ((self_14.y_12.pos <- Zls.get cstate_17.cvec !cpos_20;
                       cpos_20 := (+) !cpos_20 1)));
                  (let (result_22:bool) =
                       self_14.y_12.der <- 1.;
                       (<=) (abs_float ((-.) self_13.x_11.pos
                                             self_14.y_12.pos)) 0. in
                   cpos_20 := cindex_18;
                   (if cstate_17.major
                    then
                      (((Zls.set cstate_17.cvec !cpos_20 self_14.y_12.pos;
                         cpos_20 := (+) !cpos_20 1)))
                    else
                      (((Zls.set cstate_17.dvec !cpos_20 self_14.y_12.der;
                         cpos_20 := (+) !cpos_20 1)))); result_22)):bool) in
              let machine_15_reset self_14  =
                ((self_14.y_12.pos <- 0.):unit) in
               Node { alloc = machine_15_alloc; step = machine_15_step;
                                                reset = machine_15_reset } in
              machine_15 Node { alloc = machine_16_alloc; step = machine_16_step;
                                                          reset = machine_16_reset } in
            machine_16 in
      g_8
