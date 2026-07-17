(* The Zelus compiler, version 2024-dev
  (2026-07-7-8:20) *)
open Ztypes
type ('a) machine_58 = {mutable i_57: 'a}
type ('b, 'a) machine_55 = {mutable init_43: 'b; mutable m_40: 'a}
type ('a) machine_53 = {mutable i_52: 'a}
type ('a) machine_50 = {mutable i_49: 'a}
type ('b, 'a) machine_47 = {mutable init_42: 'b; mutable m_38: 'a}
type ('b, 'a) machine_45 = {mutable init_41: 'b; mutable m_36: 'a}
let (sum_from) =
      let sum_from_19 =
          (fun (n_20) ->
            let machine_45 = 
              let machine_45_alloc () =
                ();{ init_41 = (false:bool); m_36 = ((-1):int) } in
              let machine_45_reset self_44  =
                ((self_44.init_41 <- true):unit) in
              let machine_45_step self_44 (x_21) =
                (((if self_44.init_41 then self_44.m_36 <- n_20 else ());
                  self_44.init_41 <- false;
                  (let _fby_m_35 = self_44.m_36 in
                   let o_22 = _fby_m_35 in
                   self_44.m_36 <- (+) o_22 x_21; o_22)):int) in
               Node { alloc = machine_45_alloc;
                      reset = machine_45_reset; step = machine_45_step;
                      assertions = [] } in machine_45) in sum_from_19
let (sum_from1) =
      let sum_from1_23 =
          (fun (n_24) ->
            let machine_47 = 
              let machine_47_alloc () =
                ();{ init_42 = (false:bool); m_38 = ((-1):int) } in
              let machine_47_reset self_46  =
                ((self_46.init_42 <- true):unit) in
              let machine_47_step self_46 (x_25) =
                (((if self_46.init_42 then self_46.m_38 <- n_24 else ());
                  self_46.init_42 <- false;
                  (let _fby_m_37 = self_46.m_38 in
                   let o_26 = _fby_m_37 in
                   self_46.m_38 <- (+) o_26 x_25; o_26)):int) in
               Node { alloc = machine_47_alloc;
                      reset = machine_47_reset; step = machine_47_step;
                      assertions = [] } in machine_47) in sum_from1_23
let (main0) =
      let main0_27 =
          let machine_50 =
            let Node { alloc = i_49_alloc; step = i_49_step;
                                           reset = i_49_reset } = (sum_from 
                                                                    42) 
                                                                     in
            let machine_50_alloc () =
              ();{ i_49 = i_49_alloc () (* discrete *)  } in
            let machine_50_reset self_48  =
              (i_49_reset self_48.i_49 :unit) in
            let machine_50_step self_48 _ =
              (i_49_step self_48.i_49 1:int) in
             Node { alloc = machine_50_alloc;
                    reset = machine_50_reset; step = machine_50_step;
                    assertions = [] } in
          machine_50 in main0_27
let (main1) =
      let main1_28 =
          let machine_53 =
            let Node { alloc = i_52_alloc; step = i_52_step;
                                           reset = i_52_reset } = (sum_from1 
                                                                    42) 
                                                                     in
            let machine_53_alloc () =
              ();{ i_52 = i_52_alloc () (* discrete *)  } in
            let machine_53_reset self_51  =
              (i_52_reset self_51.i_52 :unit) in
            let machine_53_step self_51 _ =
              (i_52_step self_51.i_52 1:int) in
             Node { alloc = machine_53_alloc;
                    reset = machine_53_reset; step = machine_53_step;
                    assertions = [] } in
          machine_53 in main1_28
let (sum_from2) =
      let sum_from2_29 =
          (fun (n1_30) (n2_31) ->
            let machine_55 = 
              let machine_55_alloc () =
                ();{ init_43 = (false:bool); m_40 = ((-1):int) } in
              let machine_55_reset self_54  =
                ((self_54.init_43 <- true):unit) in
              let machine_55_step self_54 (x_32) =
                (((if self_54.init_43 then self_54.m_40 <- n1_30 else ());
                  self_54.init_43 <- false;
                  (let _fby_m_39 = self_54.m_40 in
                   let o_33 = _fby_m_39 in
                   self_54.m_40 <- (+) o_33 n2_31; o_33)):int) in
               Node { alloc = machine_55_alloc;
                      reset = machine_55_reset; step = machine_55_step;
                      assertions = [] } in machine_55) in sum_from2_29
let (main2) =
      let main2_34 =
          let machine_58 =
            let Node { alloc = i_57_alloc; step = i_57_step;
                                           reset = i_57_reset } = (sum_from2 
                                                                    42 43) 
                                                                     in
            let machine_58_alloc () =
              ();{ i_57 = i_57_alloc () (* discrete *)  } in
            let machine_58_reset self_56  =
              (i_57_reset self_56.i_57 :unit) in
            let machine_58_step self_56 _ =
              (i_57_step self_56.i_57 1:int) in
             Node { alloc = machine_58_alloc;
                    reset = machine_58_reset; step = machine_58_step;
                    assertions = [] } in
          machine_58 in main2_34
