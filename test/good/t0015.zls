(* Three different ways of counting zero-crossings. *)

let hybrid hcount1 z = c where
  rec init c = 0
  and present z -> do c = ((0 fby c) + 1) done

let hybrid hcount2 z = c where
  rec init c = 0
  and present
      | z -> do c = (last c + 1) done

let node dcount () = c where
  rec c = 0 fby (c + 1)

let hybrid main () = () where
  rec der t = 1.0 init -1.0
  and z = up(t)
  and init c1 = 0
  and present z -> do c1 = dcount () done
  and c2 = hcount1 z
  and c3 = hcount2 z

