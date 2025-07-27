(* The Zelus compiler, version 2024-dev
  (2025-06-9-16:9) *)
open Ztypes
let (f2) =
      let (f2_33:int -> int) =
          (fun ((x_34:int)) ->
            let (x_41:int) = (+) x_34 2 in
            let (x_40:int) = (+) x_34 1 in
            let (o_35:int) = (+) ((+) x_40 42) ((+) x_41 44) in
            o_35) in
      f2_33
let (f3) =
      let (f3_42:'a507 -> int) =
          (fun ((x_43:'a507)) ->
            let (f3_10_46:unit -> int) = (fun _ -> 0) in
            let (f3_10_45:unit -> int) = (fun _ -> (+) (f3_10_46 ()) 1) in
            let (f3_10_44:unit -> int) = (fun _ -> (+) (f3_10_45 ()) 1) in
            f3_10_44 ()) in
      f3_42
let (f4) =
      let (or__14_52:int -> bool) =
          (fun ((x_59:int)) -> let (o_60:bool) = false in
                               o_60) in
      let (or__14_51:int -> bool) =
          (fun ((x_55:int)) -> let (o_56:bool) = false in
                               o_56) in
      let (or__14_50:int -> bool) =
          (fun ((x_53:int)) -> let (o_54:bool) = true in
                               o_54) in
      let (or__14_49:int -> bool) =
          (fun ((x_57:int)) ->
            let (o_58:bool) = (||) (or__14_50 x_57) (or__14_51 x_57) in
            o_58) in
      let (or__14_48:int -> bool) =
          (fun ((x_61:int)) ->
            let (o_62:bool) = (||) (or__14_49 x_61) (or__14_52 x_61) in
            o_62) in
      let (f4_47:bool) = or__14_48 0 in
      f4_47
let (f5) = let f5_63 n_64 = (fun ((x_65:int)) -> (+) x_65 1) in
           f5_63
let (g) = let (g_66:int -> int) = (fun ((x_67:int)) -> (f5 42) x_67) in
          g_66
