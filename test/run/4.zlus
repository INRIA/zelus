(* TEST[-check 5] ARGS[] *)
(* Compilation of simple fbys. Expect to see 1, 2, 2, 2, 2, 2, ... *)

let node main () =
  let y = 1 fby 2 fby 2 fby 2 in
  (y = 1) -> (y = 2)

