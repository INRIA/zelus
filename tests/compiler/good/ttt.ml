(* The Zelus compiler, version 2024-dev
  (2025-05-7-12:55) *)
open Ztypes
let (f, g) =
      let rec f_10 n_12 =
              (fun ((x_13:int)) ->
                (match n_12 with
                   | 0 -> self.r_18 <- x_13
                   | _ ->
                       self.r_18 <- Stdlib.(+) x_13
                                               ((f_10 (Stdlib.(-) n_12 1)) 
                                                  x_13)
                   ); self.r_18)
              and g_11 m_14 =
                  (fun ((x_15:int)) ->
                    (f_10 (Stdlib.(-) m_14 1)) (Stdlib.(+) x_15 1))
               in
      (f_10, g_11)
let (main) =
      let (main_16:int -> int) = (fun ((x_17:int)) -> (f 4) x_17) in
      main_16
