open Owl

let main =
  let x = Mat.create 5 5 2. in
  Mat.set x 1 2 0. ;            (* set the element at (1,2) to 0. *)
  let y = Mat.get x 0 3 in

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