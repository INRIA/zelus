(* Automaton with next assignments *)

let hybrid main z = r where
  rec init r  = true
  and automaton
      | S0 -> do until z then do next r = false in S0
      end

