(* Branch reset of a derivative defined within the automaton. *)

let hybrid f z = (x, y) where
  rec init x = 0.0
  and init y = 0.0
  and automaton
      | S0 ->
          do
            der x = 1.0
          until z then do (x, y) = (1.0, 2.0) in S0

