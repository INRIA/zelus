(* The Zelus compiler, version 2024-dev
  (2026-02-23-10:13) *)
open Ztypes
let (f_3_2_11) =
      let f_3_2_12 = (fun _ -> let o_13 = (+) 2 1 in
                               o_13) in
      f_3_2_12
let (g_6_1_10) =
      let g_6_1_14 = (fun _ -> let o_15 = f_3_2_11 () in
                               o_15) in
      g_6_1_14
let (f_4) = let f_4_16 = (fun _ -> g_6_1_10 ()) in
            f_4_16
