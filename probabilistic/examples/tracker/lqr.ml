open Owl
open Lib

type vec = Mat.mat
type mat = Mat.mat

(* Using variable names matching here:
  https://en.wikipedia.org/wiki/Linear–quadratic_regulator
 *)
let lqr (a : Mat.mat) (b : Mat.mat) (q : Mat.mat) (r : Mat.mat) (n : Mat.mat) : Mat.mat =
  (* Format.printf "----------@.a:@."; *)
  (* Mat.print a; *)
  (* Format.printf "----------@.b:@."; *)
  (* Mat.print b; *)
  (* Format.printf "----------@.q:@."; *)
  (* Mat.print q; *)
  (* Format.printf "----------@.r:@."; *)
  (* Mat.print r; *)
  let p = Linalg.D.dare a b q r in
  let btp = Mat.(transpose b *@ p) in
  let f = Linalg.D.linsolve
         Mat.(r +           btp *@ b)
         Mat.(transpose n + btp *@ a)
  in Mat.(f *$ -1.)

let controller x =
    let k = lqr a_approx b q r n in
    Mat.dot k x
