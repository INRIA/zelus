
(* two versions of the switch automaton *)
let node switch1 (on1, off1) = ok where
  rec automaton
      | Off -> do ok = false until on1 then On
      | On -> do ok = true until off1 then Off

let node switch2 (on1, off1) = ok where
  rec automaton
      | Off -> do ok = false unless on1 then On
      | On -> do ok = true unless off1 then Off

let discrete choose () = let x = Random.int 2 in if x = 0 then false else true

let node check () =
  let on1 = choose () and off1 = choose () in
  switch1(on1, off1)  = switch2(false fby on1, false fby off1)
