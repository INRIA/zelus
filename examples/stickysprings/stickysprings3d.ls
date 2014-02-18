
open Stickysprings

let node world (y1, y2) =
  let rec world = (World.create (y1, y2)) fby world in
  World.update (world, y1, y2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and ((y1, y1_dot), (y2, y2_dot), pulling_force, stickiness, total) = sticky ()
  in present
     | (period (0.10)) ->
          let () = world (y1, y2) in
          plot (t, (y1, y1_dot), (y2, y2_dot), pulling_force, stickiness, total)
     else ()

