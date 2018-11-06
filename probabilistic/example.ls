let sample dist = Distribution.draw dist
let factor score x = score +. x

let node model (score, obs) = (score', a) where
  rec a = sample (Distribution.gaussian 1. 2.) fby a
  and cpt = 0. fby cpt +. a
  and score' = factor score (abs_float (obs -. cpt))


let node main () = o where
  rec cpt = 0. fby cpt +. 0.5
  and o = infer 42 model cpt
