(*
  This program should be rejected because the let/in forces an order of
  evaluation on y = x and x = y, and the latter also defines x.
  Instead, it works given a local definition (See good/t0044).
 *)
let hybrid main () = x where
  rec init x = 0.0
  and automaton
      | S1 ->
          let y = x +. 1.0 in
          do
            x = y
          done

