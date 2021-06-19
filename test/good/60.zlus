(* Hybrid automata: mixing signals and booleans in guards *)

let hybrid f (s) = x where
  rec init x = 0.0
  and 
      automaton
      | S1 ->
	  do
            der x = 1.0
	  until s() on (x > 0.5) then S2
	      (* OR, replace the type "zero" with "unit sig"
		 and use the "on" operator to combine signals
		 and booleans: *)
	      (* until s(()) on (x > 0.5) then S2 *)
      | S2 -> do der x = -1.0 done
      end

let hybrid main () = () where
  rec x = f ev
  and der t = 1.0 init -0.3 reset z -> -0.5
  and z = up(last t)
  and present (z) -> do emit ev = () done

