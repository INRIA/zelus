(* Signals on transitions of hybrid automata. *)

let hybrid f (s) = x where
  rec init x = 0.0
  and automaton
      | S1 ->
	  do
            der x = 1.0
	  until s() then S1
      end

let hybrid main () = () where
  rec x = f ev
  and der t = 1.0 init -0.3 reset z -> -0.5
  and z = up(last t)
  and present (z) -> do emit ev = () done

