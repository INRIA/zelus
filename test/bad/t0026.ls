
(* This program should be rejected because last y is not allowed in a continuous context *)
(* unless y is defined by its derivative *)

let hybrid f e = y where
  rec der t = 1.0 init -1.0 reset z -> -1.0
  and z = up(last t)

  and init y = 0
  and match e with
      | true -> do y = last y + 1 done
      | false ->
          do
            present
            | z -> do y = (let rec o = 0 -> pre o + 1 in o) done
          done

let hybrid main () =
  f true
