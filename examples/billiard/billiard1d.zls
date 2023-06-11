
(* pre: d1 <= d2 <= 0 *)

let epsilon = 0.000000001

let d2 = -. 3.0
let d1 = 2.0 *. d2 -. epsilon

let w2 = 1.0
let w1 = 2.0 *. w2

let hybrid billiard1d ((d1, w1), (d2, w2)) =
  let rec
    der x1 = v1 init d1
  and
    der x2 = v2 init d2
  and
    der v1 = 0.0 init w1
             reset (up(x1 -. x2)) -> (last v2)
  and
    der v2 = 0.0 init w2
             reset (up(x1 -. x2)) ->    (last v1)
                 | (up(x2)      ) -> -. (last v2)
  in
  ((x1, v1), (x2, v2))

(* ** plotting ** *)

open Scope

let hybrid timer v = z where
  rec der c = 1.0 init -. v reset z -> -. v
  and z = up(last c)

let node plot (t, (x1, v1), (x2, v2)) =
  let s1 = scope2 (min(d1, d2), 1.0, ("x1", linear, x1), ("x2", linear, x2))
  and s2 = scope2 (-. max(w1, w2), max(w1, w2),
             ("v1", points false, v1), ("v2", points false, v2))
  in
  window2 ("billiard1d", 8.0, t, s1, s2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and ((x1, v1), (x2, v2)) =
    billiard1d ((d1, w1), (d2, w2))
  in present
     | (timer 0.04) -> plot (t, (x1, v1), (x2, v2))
     else ()

