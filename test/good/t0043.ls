(* Derivative that depends on corresponding state variable in an automaton mode.
   See also: t0041 and t0042. *)
let hybrid main () = x where
  rec init x = 1.0
  and automaton
      | S1 ->
          do
            der x = x
          done

