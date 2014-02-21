(* TEST[-check 20] ARGS[-precisetime] *)
(* Execute a hybrid function with zero-crossings but no internal states. *)
(* For more information, add these two options to ARGS[] above:
      -lzeroc -lgcalls *)

let hybrid f () =
  present (up(1.0)) -> 1.0 else 0.0

let hybrid main () = (y = 0.0) where
  y = f()

