(* TEST[-check 20 -period] ARGS[-precisetime] *)
(* Test a signal returned from a function *)
(* For more information, add these two options to ARGS[] above:
      -lzeroc -lgcalls *)

let node f z = x where
  automaton
  | F0 -> do emit x unless z then F1 done
  | F1 -> do done

let hybrid main () = check where
  rec z1 = period (1.0)

  and present
      | z1 -> do s = f(false fby true) done

  and init c = 0
  and present
      | s() -> do c = last c + 1 done

  and check = present z1 -> ((c = 0) fby (c = 1)) else true

