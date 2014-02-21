(* TEST[-check 20 -period] ARGS[-precisetime] *)
(* Test a signal returned from a function *)
(* For more information, add these two options to ARGS[] above:
      -lzeroc -lgcalls *)

let node f z = x where
  automaton
  | F0 -> do emit x until z then F1 done
  | F1 -> do done

let hybrid g s = y where
  automaton
  | G0 -> do y = 0 until s() then G1 done
  | G1 -> do y = 1 until s() then G2 done
  | G2 -> do y = 2 until s() then G3 done
  | G3 -> do y = 3 until s() then G4 done
  | G4 -> do y = 4 until s() then G5 done
  | G5 -> do y = 5 until s() then G6 done
  | G6 -> do y = 6 done

(*
  t =   0.0    1.0    2.0    3.0    4.0  ...  10002.0
  z1=           X      X      X      X          X
  z2=    f      f      t      f      f          t
  s =    p      p      p      a      a          a
  y =    0      1      2      2      2          2

  z3=    t      t      t      t      f          f
*)

let hybrid main () = check where
  rec z1 = period (1.0)
  and z2 = present (period 2.0(10000.0)) -> true else false
  and z3 = present (period 4.0(10000.0)) -> false init true
  and present
      | z1 -> do s = f(z2) done
  and y = g(s)
  and check = z3 || y = 2

