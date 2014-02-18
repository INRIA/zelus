
let hybrid f () = y where
  rec init y = 0.0
  and automaton
      | S1 -> do der y = 1.0 until (up(y -. 5.0)) then S2
      | S2 -> let der x = 1.0 init 0.0 in
              do der y = x done
      end

let hybrid main () =
  let y = f () in
  present
    (period (0.1)) ->
       let rec t = 0.0 fby t +. 0.1 in
       let s1 = Scope.scope (0.0, 80.0, ("y", Scope.linear, y)) in
       Scope.window ("hybridaut", 8.0, t, s1)
  else ()

