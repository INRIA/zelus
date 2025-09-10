(*
    Two billiard balls and a wall:
            o->                      o|
    ----------------------------------+-----
    pos.:   x1=-2.0                 x2=0.0
    vel.:   v1=1.0                  v2=0.0

    Experiment 1: zero-crossings on positions

    Results:

    * There is a warning at the start of the simulation, and after each discrete
      reaction (e.g., to refresh the graph) that some root functions are 0
      initially. This is because ball 2 is touching the wall.

    * Three of the four relevant zero-crossings are active at the instant of
      collision:
          up(x1 - x2), for ball 1       active
          up(x2)                        inactive (ignored)
          up(x1 - x2), for ball 1       active
          up(x1)                        active
      Thus the discrete reaction swaps the velocities of balls 1 and 2. Ball 1
      comes to rest against the wall, and ball 2 travels through the wall!

    Other notes:

    * Setting the argument of timer to 0.05 or 0.10 causes the timer zero-crossing
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

let epsilon = 0.01

let hybrid billiard1d ((d1, w1), (d2, w2)) =
  let rec
    der x1 = v1 init d1 reset z12 | z21 -> last x2
  and
    der x2 = v2 init d2 reset z12 | z21 -> last x1
  and
    der v1 = 0.0 init w1 reset z12 | z21 -> last v2
  and
    der v2 = 0.0 init w2 reset z12 | z21 -> last v1 | z2 -> -. (last v2)
  and z12 = up(x1 -. x2) 
  and z21 = up(x2 -. x1)
  and z2 = up(x2 -. epsilon)
  and z = present z12 | z21 | z2 -> () in
  ((x1, v1), (x2, v2), z)

let hybrid billiard2d ((d1, w1), (d2, w2)) = ((x1, v1), (x2, v2), z)
  where rec
      automaton
      | Running ->
	  do der x1 = v1
          until z12 | z21 then do next v1 = v2 and next x1 = x2 in Running
      end
  and
     automaton
      | Running ->
	  do der x2 = v2 
          until z12 | z21 then do next v2 = v1 in Running
          else z2 then do next v2 = -. v2 in Running
      end
  and init v1 = w1
  and init v2 = w2
  and init x1 = d1
  and init x2 = d2
  and z12 = up(x1 -. x2) 
  and z21 = up(x2 -. x1)
  and z2 = up(x2 -. epsilon)
  and z = present z12 | z21 | z2 -> ()

(* ** plotting ** *)

open Scope

let node plot (t, (x1, v1), (x2, v2)) =
  let s1 =
    scope2 (min(d1, d2), 1.0, ("x1", linear, x1), ("x2", linear, x2))
  and s2 =
    scope2 (-. max(w1, w2), max(w1, w2),
      ("v1", points false, v1), ("v2", points false, v2))
  in
  window2 ("billiard_ex1", 8.0, t, s1, s2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and ((x1, v1), (x2, v2), z) =
    billiard2d ((d1, w1), (d2, w2))
  in present
     | (init) | (period(0.2)) | z() -> plot (t, (x1, v1), (x2, v2))
     else ()

