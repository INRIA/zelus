(*
   This program (re-)initializes a shared continuous state variable on entry
   into a mode.
 *)

let hybrid f () =
  let rec init x = 0.0
  and automaton
      | One -> do der x = 1.0
               until (up (x -. 2.0)) then Two
      | Two -> do der x = -1.0 until (up (-.x)) then One
      end in
  x

let hybrid main () =
  let der t = 1.0 init 0.0 in
  let x = f () in
  x

