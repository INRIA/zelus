(*
    Two billiard balls and a wall:
            o->                      o|
    ----------------------------------+-----
    pos.:   x1=-2.0                 x2=0.0
    vel.:   v1=1.0                  v2=0.0

    Experiment 2: zero-crossings on positions
                  improve on experiment 1 by eliminating the problems
                  at the initial instant.

    Results:

    * Three of the four relevant zero-crossings are active at the instant of
      collision:
          up(x1 - x2), for ball 1       active
          up(x2)                        inactive (due to if)
          up(x1 - x2), for ball 1       active
          up(x1)                        active
      Thus the discrete reaction swaps the velocities of balls 1 and 2. Ball 1
      comes to rest against the wall, and ball 2 travels through the wall!

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

  R : 1.000000e-01    0             0         0             0         1
      time            up(x1 - x2)   up(x2)    up(x1 - x2)   up(x1)    up(timer)

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
             reset (up(x1 -. x2)) ->    (last v2)
                 | (up(x1)      ) -> -. (last v1)
  and
    der v2 = 0.0 init w2
             reset (up(x1 -. x2)) -> (last v1)
                 | (up(if v2 = 0.0 then 1.0 else x2)) -> -. (last v2)
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
  window2 ("billiard_ex2", 8.0, t, s1, s2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and ((x1, v1), (x2, v2)) =
    billiard1d ((d1, w1), (d2, w2))
  in present
     | (timer 0.06) -> plot (t, (x1, v1), (x2, v2))
     else ()

