(* Different variations of automata syntax *)

let node main z = x where
  rec init y = 0
  and automaton
  | S1 -> do x = 0 done
  | S2 -> do x = 1 until z then S1 else z then S2
  | S3 -> do x = 2 then S1
  | S4 -> do x = 4 until z then S1 else z then S2
                   unless z then S3
  | S5 -> do x = 5 until z then S1 else z then S2
                   unless z then S3 else z then S5
  | S6 -> do x = 6 unless z then S3
  | S7 -> do x = 6 unless z then do y = 8 in S3
  | S8 -> do x = 7 unless z then S6 else z then S7
  | S9 -> do x = 8 until z continue S10
                   unless z continue S10
  | S10 -> do x = 8 done

