(*
    Two billiard balls and a wall:
            o->                      o|
    ----------------------------------+-----
    pos.:   x1=-2.0                 x2=0.0
    vel.:   v1=1.0                  v2=0.0

    Experiment 4: cascaded zero-crossings on velocity
                  try to model the individual collisions one after the other,
                  i.e.:   ball 1 hits ball 2
                          ball 2 hits the wall
                          ball 2 hits ball 1

    Results:

    * Works correctly:
        first zero-crossing: ball_collision
            v1=1, v2=0   -->   v1=0, v2=1
        second zero-crossing: pushed_right
            v1=0, v2=1   -->   v1=0, v2=-1
        third zero-crossing: pushed_left
            v1=0, v2=-1  -->   v1=-1, v2=0

    Issues:

    * Zero-crossing problems can be avoided by explicitly modelling specific
      cases, but this seems to defeat the purpose of simulation (i.e. to start
      with a program that is close to a simple model and to find out what
      happens). Furthermore, there is a risk that these 'problems' are not
      detected and false conclusions could be drawn from simulation results.

    Other notes:

    * Setting the timer argument to 0.05 or 0.10 causes the timer zero-crossing
      to be missed at, or just after, the instant of collision. The timer state
      then increases without bound and there are no more discrete reactions to
      refresh the plot.

      It seems that the zero-crossings for the collision occur just before the
      timer state is due to hit zero, and then the solver is reset (after the
      discrete reaction), and, afterward, zero-crossings at or very close to the
      new starting instant are ignored (case (nst == 0) in CVode, which calls
      CVRcheck1).

 *)

(*
  Logging:

  I : 0.000000e+00     0.000000e+00    1.000000e+00    0.000000e+00   -2.000000e+00   -5.000000e-02
      time             v2              v1              x2             x1              timer

  R : 1.000000e-01    0             0               0                 1
      time            _pushed_left  _pushed_right   ball_collision    up(timer)

  I  - initial instant
  C' - state values at start of discrete instant (i.e. last values from solver)
  R  - zero-crossing values that triggered a discrete instant
  D  - state values after a discrete instant (i.e. values from program)
  C  - state values after a continuous step (before another continuous step)
*)

(* pre: d1 <= d2 <= 0 *)

let d1 = -. 2.0
let d2 = 0.0

let w1 = 1.0
let w2 = 0.0

let hybrid billiard1d ((d1, w1), (d2, w2)) =
  let rec
    der x1 = v1 init d1
  and
    der x2 = v2 init d2
  and
    der v1 = 0.0 init w1
             reset 
             | ball_collision -> (last v2)
             | ball2_pushed_left ->
                 (if balls_touching then last v2 else last v1)
  and
    der v2 = 0.0 init w2
             reset
             | ball_collision -> (last v1)
             | ball2_pushed_right ->
                (if x2 >= 0.0 then -. (last v2) else last v2)
             | ball2_pushed_left ->
                (if balls_touching then last v1 else last v2)
  and
    ball_collision = up(x1 -. x2)
  and
    ball2_pushed_right = up(if v2 <= 0.0 then -. 1.0 else 1.0)
  and
    ball2_pushed_left  = up(if v2 >= 0.0 then -. 1.0 else 1.0)
  and
    balls_touching = (x1 -. x2 >= 0.0)
  in
  ((x1, v1), (x2, v2))

(* ** plotting ** *)

open Scope

let hybrid timer v = z where
  rec der c = 1.0 init -. v reset z -> -. v
  and z = up(c)

let node plot (t, (x1, v1), (x2, v2)) =
  let s1 =
    scope2 (min(d1, d2), 1.0, ("x1", linear, x1), ("x2", linear, x2))
  and s2 =
    scope2 (-. max(w1, w2), max(w1, w2),
      ("v1", points false, v1), ("v2", points false, v2))
  in
  window2 ("billiard_ex4", 8.0, t, s1, s2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and ((x1, v1), (x2, v2)) =
    billiard1d ((d1, w1), (d2, w2))
  in present
     | (timer 0.06) -> plot (t, (x1, v1), (x2, v2))
     else ()

