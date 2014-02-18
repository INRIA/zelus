(*
  No derivative must appear on a transition
*)

let hybrid main (z) =
  let rec
  automaton
  | One -> do der x = 1.0 init 0.0 until z then do der k = 2 in Two
  | Two -> do der x = 1.0 init 0.0 done
  end in
  ()

