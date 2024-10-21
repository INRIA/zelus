(*
   This program should be rejected because x is not initialized
   in all states of the automaton (inside a let statement).
 *)

let hybrid main () =
  let rec
      der time = 1.0 init 0.0
  and
      automaton
      | One -> do der x = 1.0 done
      | Two -> do der x = 1.0 init 0.0 done
      in
  ()

