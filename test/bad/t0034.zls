(* TEST[-check 20] *)

(*
  This example should be rejected because blocks (such as that guarded by
  trigger in this example) are scheduled as a unit, i.e., they are not split up
  into individual equations. There is thus a cyclic dependency:
      v <- s <- r <- ignore <-same block- v
*)

let hybrid toggle change = v where
  rec automaton
      | Off -> do v = 1.0 until change(1) then On
      | On  -> do v = 2.0 done

let node ignore (x, y) = ()

let f () = 1

let hybrid main () = check where
  rec trigger = period (1.0)
  and present trigger ->
        local v in do
            v = f ()
        and emit s = v
        and () = ignore (v, r)
      done
  and r = toggle s
  and check = present trigger -> (true -> r = 2.0) else true

