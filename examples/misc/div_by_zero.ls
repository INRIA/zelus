(* What happen when the state variable is undefined after the zero-crossing point *)

let n = sqrt(-1.0)

let hybrid f () = x where
  rec init x = 0.0
  and init y = 1.0
  and automaton
      | S1 -> do z = sqrt(y) and der y = -1.0 and der x = -1.0
              until (up(-. y)) then (* do x = n in *) S2 done
      | S2 -> do z = 0.0 and der y = -1.0 and der x = 0.0 done

(* The main function *)
let hybrid main () =
  let der t = 1.0 init 0.0 in
  let y = f () in
  present (period (0.1)) ->
      (let s = Scope.scope (-12.0, 12.0, ("y", Scope.linear, y))
      in Scope.window ("updown", 60.0, t, s));
  ()
