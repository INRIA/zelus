(* TEST[-check 20 -period] ARGS[] *)
(* Detect signal from function inside block *)

let node emitsig () = x where
  emit x = ()

let node main () = check where
  rec automaton
  | S0 -> do
                s = emitsig ()
            and () = print_endline "S0"
            and check = true -> false
          until s() then S1 done

  | S1 -> do
                check = true
            and () = print_endline "S1"
          done

