open Owl

let main =
  let x = Mat.create 5 5 2. in
  Mat.set x 1 2 0. ;            (* set the element at (1,2) to 0. *)
  (*let y = Mat.get x 0 3 in*)

  Mat.iteri_rows (fun i r ->
    Printf.printf "row %i: %.1f\n" i (Mat.sum' r)
  ) x

(* Using variable names matching here:
  https://en.wikipedia.org/wiki/Linear–quadratic_regulator
 *)
let lqr (a : Mat.mat) (b : Mat.mat) (q : Mat.mat) (r : Mat.mat) (n : Mat.mat) : Mat.mat =
  let p = Linalg.D.dare a b q r in
  let btp = Mat.(transpose b *@ p) in
  let f = Linalg.D.linsolve
         Mat.(r +           btp *@ b)
         Mat.(transpose n + btp *@ a)
  in Mat.(f *$ -1.)


(* State is: p1 p2 v1 v2 a1 a2 *)
(* The average dynamics *)
let a_ex (dt : float) : Mat.mat = Mat.of_arrays
  [| [| 1. ; 0. ; 0. ; 0. ; 0. ; 0. |]
  ;  [| 0. ; 1. ; 0. ; 0. ; 0. ; 0. |]
  ;  [| dt ; 0. ; 1. ; 0. ; 0. ; 0. |]
  ;  [| 0. ; dt ; 0. ; 1. ; 0. ; 0. |]
  ;  [| 0. ; 0. ; dt ; 0. ; 1. ; 0. |]
  ;  [| 0. ; 0. ; 0. ; dt ; 0. ; 1. |] |]

(* There are two controls for each axis of acceleration *)
let b_ex : Mat.mat = Mat.of_arrays
  [| [| 0. ; 0. ; 0. ; 0. ; 1. ; 0. |]
  ;  [| 0. ; 0. ; 0. ; 0. ; 0. ; 1. |] |]

let q_ex : Mat.mat = Mat.of_arrays
  [| [| 1. ; 0. ; 0. ; 0. ; 0. ; 0. |]
  ;  [| 0. ; 1. ; 0. ; 0. ; 0. ; 0. |]
  ;  [| 0. ; 0. ; 0. ; 0. ; 0. ; 0. |]
  ;  [| 0. ; 0. ; 0. ; 0. ; 0. ; 0. |]
  ;  [| 0. ; 0. ; 0. ; 0. ; 0. ; 0. |]
  ;  [| 0. ; 0. ; 0. ; 0. ; 0. ; 0. |] |]

let r_ex : Mat.mat = Mat.of_arrays
  [| [| 1. ; 0. |]
  ;  [| 0. ; 1. |] |]

let n_ex : Mat.mat = Mat.zeros 6 2

let lqr_ex (dt : float) : Mat.mat =
  lqr (a_ex dt) b_ex q_ex r_ex n_ex

let controller (dt : float) (pos : float array) (vel : float array) (acc : float array) : float * float =
  let lqr_f = lqr_ex dt in
  let x_arr = Array.concat [pos; vel; acc] in
  let x = Mat.of_array x_arr 6 1 in
  let u = Mat.(lqr_f *@ x) in
  (Mat.get u 0 0, Mat.get u 1 0)