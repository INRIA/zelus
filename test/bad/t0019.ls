(*
  The variable x may not be defined outside the automaton
  (by der x = ... in ...) and inside (by the x = ... on the transition).
 *)

let hybrid main () = x where
  rec der x = 1.0 init -1.0
  and automaton
      | S -> do until (up(x)) then do x = -1.0 in S
      end

