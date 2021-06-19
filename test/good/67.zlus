(* der with reset on local variable inside automaton *)

let hybrid main () = () where
  rec
      init y = 0.0
  and
      automaton
      | Apart ->
          local r in
          do
            der y = 1.0 reset r -> 2.0
          and r = up(last y)
          done

