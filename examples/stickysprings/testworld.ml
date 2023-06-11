
let p1_min = 0.0
let p1_max = 1.5
let p2_min = 1.5
let p2_max = 3.0

let test () =
  let p1 = ref 1.5 in
  let p1_dot = ref 0.2 in

  let p2 = ref 1.5 in
  let p2_dot = ref (-0.2) in

  let world = World.create !p1 !p2 in

  while true do
    Unix.sleep 1;

    p1 := !p1 +. !p1_dot;
    p2 := !p2 +. !p2_dot;

    if !p1 <= p1_min then (p1_dot := -. !p1_dot; p1 := p1_min);
    if !p1 >= p1_max then (p1_dot := -. !p1_dot; p1 := p1_max);
    if !p2 <= p2_min then (p2_dot := -. !p2_dot; p2 := p2_min);
    if !p2 >= p2_max then (p2_dot := -. !p2_dot; p2 := p2_max);

    Printf.printf "sending state: %e %e\n" !p1 !p2;
    flush stdout;
    World.update world !p1 !p2
  done

let _ = test ()

