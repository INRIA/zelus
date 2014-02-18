open Data
open Misc

let dt = 0.01 (* s     *)
let l = 15.0 (* m     *)
let g = 10.0 (* m/s^2 *)
let b = 1.5  (* 1/s *)
(* mass of the pendulum *)
let m = 5.

let node integr(x') = Misc.integr(dt, x')
let node deriv(x) = Misc.deriv(dt, x)

(*
  equation of the pendulum  :
  - theta angle of the pendulum with Oy
  - d2x0,d2y0 second degree derivatives of the botom coordinates
  - l length of the pendulum
  - g acceleration  *)
let node pendulum(theta0, x'', y'') = theta where
  rec
      theta = integr(integr((sin thetap) *. (y'' +. g *. m)
                            -.(cos thetap) *. x'') /. l)
  and
      thetap = theta0 fby theta
  
(* Second version with loss in energy *)
let node pendulum_with_loss (theta0, x0'', y0'') = theta where
  rec
      theta = integr(integr((sin thetap) *. (y0'' +. g *. m)
                              -.(cos thetap)*. x0'') /. l
                       -. b *. thetap)
  and
      thetap = theta0 fby theta
  

let node mpendulum(theta0, x0, y0) =
(* pendulum controled by hand:        *)
(* x0, y0 are the botom coordinates   *)
  
(* derivation *)
  
  let x0'' = deriv (deriv x0) in
  let y0'' = deriv (deriv y0) in
  
(* pendulum *)
  
  let theta = pendulum_with_loss(theta0, x0'', y0'') in
  
(* geometry *)
  
  let x = x0 +. l*. (sin theta) in
  let y = y0 +. l*. (cos theta) in
  (x0, y0, x, y, theta)
    
let node manual () =
  let x0,y0 = get_cursor () in
  let (x0, y0, x, y, _) = mpendulum(0.0, x0, y0) in 
  let p = make_pend(x0, y0, x, y) in
  draw_pendulum(p, p -> pre p)
