(* The Zelus compiler, version 2024-dev
  (2025-06-9-16:9) *)
open Ztypes
type machine_4 = unit
let (g) =
      let g_3 =
          let machine_4 cstate_5 = 
             let machine_4_alloc _ = () in
            let machine_4_step self _ =
              (((if cstate_5.major then () else ()); 1.):float) in
            let machine_4_reset self  =
              (():unit) in
            Node { alloc = machine_4_alloc; step = machine_4_step;
                                            reset = machine_4_reset } in
            machine_4 in
      g_3
