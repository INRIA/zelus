open Basics

(* [ground x] returns the position in [y] *)
(* let ground x = World.ground(x) *)

let node sc6 (yl, yu,
         (n1, t1, v1),
                        (n2, t2, v2),
                        (n3, t3, v3),
                        (n4, t4, v4),
                        (n5, t5, v5),
                        (n6, t6, v6)
) =
  let
  rec s1 = (Gtkplot.signal (n1, t1)) fby s1
  and s2 = (Gtkplot.signal (n2, t2)) fby s2
  and s3 = (Gtkplot.signal (n3, t3)) fby s3
  and s4 = (Gtkplot.signal (n4, t4)) fby s4
  and s5 = (Gtkplot.signal (n5, t5)) fby s5
  and s6 = (Gtkplot.signal (n6, t6)) fby s6
  and sc = (Gtkplot.scope (yl, yu,
       cons (s1, (cons (s2, cons (s3, cons (s4, cons ( s5, singleton s6))))))))
           fby sc
  in
  Gtkplot.update (s1, v1);
  Gtkplot.update (s2, v2);
  Gtkplot.update (s3, v3);
  Gtkplot.update (s4, v4);
  Gtkplot.update (s5, v5);
  Gtkplot.update (s6, v6);
  sc

let pi = 3.1416
let mp6 = -. (pi /. 6.)
let g = 9.80665
let l = 0.2

let pinit0 = mp6
let pinit1 = 0.0
let pinit2 = 0.0

let acc x = -. g /. l *. (sin x)

(* Main entry point *)
let hybrid cradle () =
  let
  rec der p0 = v0 init pinit0 reset hit01 -> last p1
  and der v0 = acc (p0) init 0.0 reset hit01 -> last v1

  and der p1 = v1 init pinit1 reset hit01 -> last p0 | hit12 -> last p2
  and der v1 = acc (p1) init 0.0 reset hit01 -> last v0 | hit12 -> last v2

  and der p2 = v2 init pinit2 reset hit12 -> last p1
  and der v2 = acc (p2) init 0.0 reset hit12 -> last v1

  (* and hit01 = up (if (last p0 -. last p1) > 0.0 then 1.0 else -)1.0) *)
  (* and hit12 = up (if (last p1 -. last p2) > 0.0 then 1.0 else -1.0) *)
  and hit01 = up (last p0 -. last p1)
  and hit12 = up (last p1 -. last p2)

  and h1 = present hit01 -> -1.0 *. last h1 init -0.1
  and h2 = present hit12 -> -1.0 *. last h2 init -0.1

  in p0, p1 +. 1.0 , p2 +. 2.0 , h1, h2 


let hybrid main () =
  let der t = 1.0 init 0.0 in
  let p0, p1, p2, h1, h2 = cradle () in
  present (period (0.05)) ->
      let s = sc6 (-1.0, 3.0,
         ("p0", Scope.linear, p0),
         ("h1,", Scope.linear, h1 +. 0.5),
         ("p1", Scope.linear, p1),
         ("h2,", Scope.linear, h2 +. 1.5),
         ("p2", Scope.linear, p2),
         ("", Scope.linear, -0.6)
   )
      in Scope.window ("cradle3", 3.0, t, s)

  else ()

