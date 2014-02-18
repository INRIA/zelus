(* Derivative that depends on corresponding state variable through the
   intermediary of a variable local to an automaton mode.
   See also: t0041, t0042, and t0043. *)
let hybrid main () = x where
  rec init x = 0.0
  and automaton
      | S1 ->
          local y in
          do
            y = x and der x = y
          done

