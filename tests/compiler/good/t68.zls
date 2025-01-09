(* discrete reset of a tuple inside an automaton *)

let hybrid main () = () where
  rec
      init y = (0.0, 0.1)
  and
      automaton
      | Apart ->
          local r in
          do
            present r -> do y = (2.0, 2.1) done
            and r = up(1.0)
          done

