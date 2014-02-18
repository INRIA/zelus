(*
 *
 * 3 balls Newton pendulum using a limit soft interaction model.
 *
 * $Id$
 *
 *)

open Basics

let node sc3 (yl, yu,
         (n1, t1, v1),
         (n2, t2, v2),
         (n3, t3, v3)
) = (
  let
  rec s1 = (Gtkplot.signal (n1, t1)) fby s1
  and s2 = (Gtkplot.signal (n2, t2)) fby s2
  and s3 = (Gtkplot.signal (n3, t3)) fby s3
  and sc = (Gtkplot.scope (yl, yu,
       cons (s1, (cons (s2, (singleton s3))))))
           fby sc
  in
  Gtkplot.update (s1, v1);
  Gtkplot.update (s2, v2);
  Gtkplot.update (s3, v3);
  sc
)

let pi = 4. *. (atan 1.0)

let l = 0.2

let g0 = 9.81

let f0 = 1.0

(* true when x > 0, false otherwise *)
let hybrid switch(x) = ok where
  automaton
  | False -> do ok = false until up(if x > 0.0 then 1.0 else -1.0) then True done
  | True -> do ok = true until up(-. (if x > 0.0 then 1.0 else -1.0)) then False done

let k = -0.33

let hybrid clock suspend = t where
  init t = 0.
  and
    automaton
      | Run -> do der t = 1. until up(if suspend then 1.0 else -1.0) then Hold done
      | Hold -> do der t = 0. until up(if suspend then -1.0 else 1.0) then Run done

let hybrid cradle (theta01, theta02, theta03) (* initial positions *) =
  let rec der theta1 = omega1 init theta01 
  and der theta2 = omega2 init theta02 
  and der theta3 = omega3 init theta03 
  and der omega1 = (if collide then 0.0 else k *. sin theta1) -. alpha12
  and der omega2 = (if collide then 0.0 else k *. sin theta2) +. alpha12 -. alpha23
  and der omega3 = (if collide then 0.0 else k *. sin theta3) +. alpha23
  and alpha12 = if collide12 then 10.0 else 0.0
  and alpha23 = if collide23 then 10.0 else 0.0
  and collide12 = switch(theta1 -. theta2)
  and collide23 = switch(theta2 -. theta3)
  and collide = collide12 or collide23
  in (theta1, theta2, theta3, collide)

let hybrid main () =
  (* let der t = 1.0 init 0.0 in *)
  let p0, p1, p2, collide = cradle (-. pi /. 6., -. pi /. 24. , pi /. 6.) in
  let t = clock collide in
  present (period (0.05)) ->
      let s = sc3 (-1.0, 3.0,
         ("p0", Scope.linear, p0),
         ("p1", Scope.linear, p1),
         ("p2", Scope.linear, p2)
   )
  in Scope.window ("cradle3soft", 3.0, t, s)

  else ()
