
(* This program should be rejected because there are two init expressions for y.
   Compilation gives invalid ML. *)

let node f (e, z) = y where
  rec init y = 0
  and match e with
      | true -> do y = 0 done
      | false ->
          do
            present
            | z -> do y = (let rec o = 0 -> pre o + 1 in o) done
          done

let node main () =
  f(true, true)
