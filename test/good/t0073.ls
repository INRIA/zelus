(* calling a hybrid function without continuous states from inside a block,
   compare with t0072. *)
let hybrid f x = up(x)

let hybrid test z = () where
  rec init x = -1.0
  and match z with
      | true ->  do der x =  0.0 and z2 = f(x) done
      | false -> do der x =  1.0 and z2 = f(x) done

