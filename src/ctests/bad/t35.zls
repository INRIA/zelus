(*
  This example should be rejected because there is a causality cycle between the
  two automata. Statically, received is needed to determine the status of sent,
  and sent is needed to determine the presence of received.
*)

let hybrid f z = () where
  rec automaton
      | S0 -> do until received() then do emit sent = () in S0

  and automaton
      | T0 -> do until sent() then T1
      | T1 -> do until z then do emit received = () in T0

