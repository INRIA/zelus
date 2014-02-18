(*
  In the current version of Zélus, automata are compiled as monolithic blocks;
  that is, the variables they define are not separated out into separate
  definitions. The causality analysis must thus reject this program because
  there is a cyclic dependency:

    * the status of received is defined by the second automaton and it is
      required to execute the first automaton.

    * the status of sent is defined by the first automaton and it is
      required to execute the second automaton.
*)

let hybrid channel () = (sent, received) where
  rec automaton
      | Sending ->
          local t in
          do der t = 1.0 init -.1.0
          until up(t) then do emit sent = () in Ack
      | Ack ->
          do
          until received() then Sending

  and automaton
      | Wait ->
          do
          until sent() then Receiving
      | Receiving ->
          local t in
          do der t = 1.0 init -.0.1
          until up(t) then do emit received = () in Wait

