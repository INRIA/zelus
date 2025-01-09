(* passing a pair to a parameterised state *)

let getpair () = (1.0, 2.0)

let hybrid f () = y where
  rec init y = -1.0
  and automaton
      | S0 -> do
            der y = 1.0
          until (up(y)) then let x,y = getpair () in S1(x,y)
          else (up(y)) then S1(1.0, 2.0)
      | S1(x1, x2) -> 
	   do der y = x1 +. x2
           done
      end
