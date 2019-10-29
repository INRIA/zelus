(* https://peterroelants.github.io/posts/multivariate-normal-primer/ *)

open Probzelus
open Owl
open Distribution

type vector = Mat.mat
type matrix = Mat.mat

let mvgaussian_sampler mu sigma () =
  let u, s, _ = Linalg.Generic.svd sigma in 
  let a = Mat.(u *@ (sqrt (diagm s))) in 
  let n = (Arr.shape mu).(0) in
  let xs = Arr.gaussian ~mu:0. ~sigma:1. [| n; 1 |] in
  Mat.(mu + a *@ xs)

let mvgaussian_scorer mu sigma x =
  let two_pi = 2.0 *. 3.14159265358979323846 in
  let d = float (Arr.shape x).(0) in
  let x_m = Mat.(x - mu) in
  -. 0.5 *. log (two_pi ** d *. Linalg.D.det sigma)
  -. 0.5 *. Mat.(get (transpose (Linalg.D.linsolve sigma x_m) *@ x_m) 0 0)

let mvgaussian (mu, sigma) =
  Dist_sampler (mvgaussian_sampler mu sigma, mvgaussian_scorer mu sigma)

let print_vector v =
  Arr.print v;
  flush stdout

(* let mu = Mat.of_arrays [| [| 0.; |]; *)
(*                           [| 1.; |]; |] *)

(* let sigma = Mat.of_arrays [| [| 1.0; 0.8; |]; *)
(*                              [| 0.8; 1.0; |] |] *)

(* let score x y = *)
(*   let v = Mat.of_arrays [| [| x; |]; *)
(*                            [| y; |]; |] in *)
(*   let s = mvgaussian_scorer mu sigma v in *)
(*   Format.printf "XXXXXXXX %f %f = %f@." x y (exp s) *)

(* let () = *)
(*   score 0. 1.; *)
(*   score 0. 0.; *)
(*   score 100. 100.; *)
(*   score (-1.) 0.; *)
(*   score (-1.) (-0.5); *)
(*   score (1.) (2.0); *)
(* ;; *)


(* let () = *)
(*   Graphics.open_graph " 800x800"; *)
(*   Graphics.draw_segments [| 400, 0, 400, 800 |]; *)
(*   Graphics.draw_segments [| 0, 400, 800, 400 |]; *)
(*   for _ = 1 to 100_000 do *)
(*     let v = mvgaussian_sampler mu sigma () in *)
(*     let x = Arr.get v [|0; 0|] in *)
(*     let y = Arr.get v [|1; 0|] in *)
(*     Graphics.plot *)
(*       (int_of_float (100. *. x +. 400.)) *)
(*       (int_of_float (100. *. y +. 400.)) *)
(*   done; *)
(*   ignore (read_line ()) *)
(* ;; *)

