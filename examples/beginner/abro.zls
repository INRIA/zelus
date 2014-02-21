(* the ABRO example (Berry, "Constructive Semantics of Esterel" *)
(* await for inputs A and B *)
(* - emits O when A and B has been received *)
(* - resets the behavior every time R is true *)

let node expect x = o where
  automaton
      Await -> do o = false unless x then Run
    | Run -> do o = true done

let node abo (a, b) = o where
  rec automaton
      | Await ->
          do o = (expect a) & (expect b)
          until o then Stop
      | Stop ->
          do o = false done

let node abro (a, b, r) = o where
  reset
    o = abo (a, b)
  every r


let node abro1 (a, b, r) = o where 
  rec 
    reset
      automaton
      | Await ->
          do o = (expect a) & (expect b)
          until o then Stop
      | Stop ->
          do o = false done
    every r
      
let node abro2 (a, b, c, d, e, r) = o where
  rec
    reset
      automaton
      | Await ->
          do o = (expect a) & (expect b) & (expect c) & 
            (expect d) & (expect e)
          until o then Stop
      | Stop ->
          do o = false done
   every r
      
let node main () =
  let rec a = false fby true fby false fby true fby false fby b
  and b = false fby false fby true fby false fby false fby e
  and c = false fby true fby true fby a
  and d = false fby false fby true fby false fby true fby b
  and e = false fby true fby b
  and r = false fby false fby false fby false fby false fby false fby
          false fby false fby false fby false fby false fby false fby
          true
  and o = abro2 (a, b, c, d, e, r)
  in
  if o then print_endline "output!" else ()

