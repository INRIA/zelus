let node count(n, top) = (cpt = 0) where
  rec cpt = n -> (pre cpt - 1) mod n

let node count_every_c(n, top) = o where
  rec
     reset
       o = count(n, top)
     every (nat = 10)
  and
     nat = 0 -> pre nat + 1

let node mouse(click, top) = (simple, double) where
  rec
      automaton
      | Await -> do until click then Counting
      | Counting -> 
          do until click then do emit double in Await
          else (count(4, top)) then do emit simple in Await
      end

