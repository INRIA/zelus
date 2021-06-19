(* Reset of internal derivative on transition: do <reset> in <state> *)

let hybrid main () = x where rec
  init x = -1.0
  and automaton
      | S ->
	  do
            der x = 1.0
	  until (up(last x)) then do x = -1.0 in S
      end

