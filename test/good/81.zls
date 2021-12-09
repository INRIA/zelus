(* ordonnancement et fusion des conditionnelles *)
let node f(x) = (o1, o2, o3, o, o') where
  rec
      o1 = o2 + 2
  and o2 = o3 - 0 -> pre o1
  and o3 = 4 + 0 fby o3
  and match x with | true -> do o = o3 done | false -> do o = 1 done
  and o4 = o + 2
  and match x with | true -> do o' = 2 done | false -> do o' = o3 done
