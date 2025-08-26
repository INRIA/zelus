(* The Zelus compiler, version 2024-dev
  (2025-05-7-12:55) *)
open Ztypes
type ('b, 'a) machine_26 = {mutable cstate_39: 'b; mutable x_19: 'a}
type ('b, 'a) machine_25 = {mutable cstate_33: 'b; mutable y_20: 'a}
type ('b, 'a) machine_22 = {mutable cstate_27: 'b; mutable x_15: 'a}
let (h) =
      let h_12 =
          (fun  ->
            let machine_22 = 
              let machine_22_alloc (cstate_27) =
                cstate_27.cmax <- 1;
                { cstate_27 = (cstate_27:Ztypes.cstate);
                  x_15 = { pos = (-1.); der = 0. } } in
              let machine_22_step self_21 (x1_13, x2_14) =
                ((let cindex_28 = cstate_27.cindex in
                  let cpos_30 = ref (cindex_28:int) in
                  self_21.cstate_27.cindex <- (+) self_21.cstate_27.cindex 1;
                  (if self_21.cstate_27.major
                   then
                     for i_2 = cindex_28 to 0
                     do Zls.set self_21.cstate_27.dvec i_2 0. done
                   else
                     ((self_21.x_15.pos <- Zls.get self_21.cstate_27.cvec
                                                   !cpos_30;
                       cpos_30 := (+) !cpos_30 1)));
                  (let result_32 = self_21.x_15.der <- 1.; self_21.x_15.pos in
                   cpos_30 := cindex_28;
                   (if self_21.cstate_27.major
                    then
                      (((Zls.set self_21.cstate_27.cvec
                                 !cpos_30 self_21.x_15.pos;
                         cpos_30 := (+) !cpos_30 1)))
                    else
                      (((Zls.set self_21.cstate_27.dvec
                                 !cpos_30 self_21.x_15.der;
                         cpos_30 := (+) !cpos_30 1)))); result_32)):float) in
              let machine_22_reset self_21  =
                ((self_21.x_15.pos <- 0.):unit) in
               Node { alloc = machine_22_alloc;
                      step = machine_22_step; reset = machine_22_reset;
                      assertions = [] } in machine_22) in h_12
let (g) =
      let g_16 =
          (fun  ->
            let machine_26 = 
              let machine_26_alloc (cstate_39) =
                cstate_39.cmax <- 1;
                { cstate_39 = (cstate_39:Ztypes.cstate);
                  x_19 = { pos = (-1.); der = 0. } } in
              let machine_26_step self_23 (x1_17, x2_18) =
                ((let cindex_40 = cstate_39.cindex in
                  let cpos_42 = ref (cindex_40:int) in
                  self_23.cstate_39.cindex <- (+) self_23.cstate_39.cindex 1;
                  (if self_23.cstate_39.major
                   then
                     for i_2 = cindex_40 to 0
                     do Zls.set self_23.cstate_39.dvec i_2 0. done
                   else
                     ((self_23.x_19.pos <- Zls.get self_23.cstate_39.cvec
                                                   !cpos_42;
                       cpos_42 := (+) !cpos_42 1)));
                  (let result_44 =
                       self_23.x_19.der <- 1.;
                       (let _ = () in
                        self_23.x_19.pos) in
                   cpos_42 := cindex_40;
                   (if self_23.cstate_39.major
                    then
                      (((Zls.set self_23.cstate_39.cvec
                                 !cpos_42 self_23.x_19.pos;
                         cpos_42 := (+) !cpos_42 1)))
                    else
                      (((Zls.set self_23.cstate_39.dvec
                                 !cpos_42 self_23.x_19.der;
                         cpos_42 := (+) !cpos_42 1)))); result_44)):float) in
              let machine_26_reset self_23  =
                ((self_23.x_19.pos <- 0.):unit) in
              let machine_26 = 
                let machine_26_alloc (cstate_33) =
                  cstate_33.cmax <- 1;
                  { cstate_33 = (cstate_33:Ztypes.cstate);
                    y_20 = { pos = (-1.); der = 0. } } in
                let machine_26_step self_24 self_23 =
                  ((let cindex_34 = cstate_33.cindex in
                    let cpos_36 = ref (cindex_34:int) in
                    self_24.cstate_33.cindex <- (+) self_24.cstate_33.cindex
                                                    1;
                    (if self_24.cstate_33.major
                     then
                       for i_2 = cindex_34 to 0
                       do Zls.set self_24.cstate_33.dvec i_2 0. done
                     else
                       ((self_24.y_20.pos <- Zls.get self_24.cstate_33.cvec
                                                     !cpos_36;
                         cpos_36 := (+) !cpos_36 1)));
                    (let result_38 =
                         self_24.y_20.der <- 1.;
                         (<=) (abs_float ((-.) self_23.x_19.pos
                                               self_24.y_20.pos)) 0. in
                     cpos_36 := cindex_34;
                     (if self_24.cstate_33.major
                      then
                        (((Zls.set self_24.cstate_33.cvec
                                   !cpos_36 self_24.y_20.pos;
                           cpos_36 := (+) !cpos_36 1)))
                      else
                        (((Zls.set self_24.cstate_33.dvec
                                   !cpos_36 self_24.y_20.der;
                           cpos_36 := (+) !cpos_36 1)))); result_38)):
                  bool) in
                let machine_26_reset self_24  =
                  ((self_24.y_20.pos <- 0.):unit) in
                 Node { alloc = machine_26_alloc;
                        step = machine_26_step; reset = machine_26_reset;
                        assertions = [] } in Node { alloc = machine_26_alloc;
                                                    step = machine_26_step;
                                                    reset = machine_26_reset;
                                                    assertions = [machine_25] } in
          machine_26) in
g_16
