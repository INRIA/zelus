(* calling a hybrid function without zero-crossings, but with continuous states,
   from inside a block, compare with t0072 and t0073. *)

let hybrid f() = x where
  der x = 1.0 init 0.0

let hybrid test z = () where
  match z with
  | true ->  do x = 0.0 done
  | false -> do x = f () done

