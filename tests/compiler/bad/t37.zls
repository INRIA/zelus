(* This example is rejected because of a causality loop. One has to *)
(* write [do y = last x] and [do x = last y] *)
(* This program could be considered causal as it is enough to add *)
(* [x = last x] in the first handler to make it causal. *)
(* I prefer to reject it in favor of a more explicit writting rule *)
let node f(t) = (x,y, r, z) where
  rec match t with
      | true -> do y = x done
      | false -> do x = y done
  and init y = 0 and init x = 0
  and r = x + 1
and z = y + 2
