(*
   This program should be rejected because the derivatives of [x]
   is given in parallel with a possible reset of [x].

   Write instead:

     rec der x = 1.0 init 0.0 reset z -> 1.0

 *)

let hybrid f z = x where
  rec der x = 1.0 init 0.0
  and automaton
      | S0 ->
          do
          until z then do x = 1.0 in S0

