(* The Zelus compiler, version 2024-dev
  (2025-06-9-16:9) *)
open Ztypes
let (f) =
      let f_12 =
          (fun (x_13) -> let z_15 = 2 in
                         let y_14 = 1 in
                         (+) y_14 z_15) in
      f_12
type t = {x: int; y: int}
let (g) =
      let g_18 = (fun (x_19) -> let x1_20 = 2 in
                                (+) x_19.x x_19.y) in
      g_18
