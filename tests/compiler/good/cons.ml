(* The Zelus compiler, version 2024-dev
  (2026-04-9-18:31) *)
open Ztypes
let (main1) =
      let (f_13:'_d -A-> [4]'_d -A-> [1+4]'_d) =
          (fun ((x_14:'_d)) ((y_15:[4]'_d)) ->
            (let _t = Array.make (1+4) [|x_14|].(0) in 
            Array.blit [|x_14|] 0 _t 0 1;  Array.blit y_15 0 _t 4;  _t)) in
      let (main1_12:'_d -A-> [4]'_d -A-> [1+4]'_d) = f_13 in
      main1_12
