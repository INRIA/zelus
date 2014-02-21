(* TEST[-check 1000] ARGS[] *)
(* Check a basic derivative against expected values at regular intervals. *)

open Basics

let hybrid time () = t where
  der t = 1.0 init 0.0

let hybrid main () = obs where
  rec
      t = time ()
  and
      obs = present (period (0.5)) ->
            (let rec n = 0 fby n + 1 in
             let () = print_string "t=" in
             let () = print_float t in
             let () = print_string " =?= " in
             let () = print_float (float(n) *. 0.5) in
             let () = print_string " (" in
             let () = print_int n in
             let () = print_string ")\n" in
             float(n) *. 0.5 =~= t)
            init true

