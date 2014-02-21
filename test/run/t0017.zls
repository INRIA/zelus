(* TEST[-check 1000] ARGS[] *)

let hybrid k () = x where rec
   init x = 0.0
  and
   automaton
   | S1 ->
       local s in
       do der s = 1.0 init last x and x = s
       until (up(x -. 10.0)) then S2 done
   | S2 ->
       local s in
       do der s = -1.0 init last x and x = s
       until (up(-.(x +. 10.0))) then S1 done

(*
let hybrid main () =
  let o = k () in
  true *)

let hybrid main () = true where
  rec o = k ()
  and
  () = present
       | (period (0.01)) ->
           let () = print_float o in print_newline ()
       init ()


(*
type discontinuous = { v: float; change: zero }

let hybrid k_with_stops () = { v = x; change = z } where rec
   init x = 0.0
  and
   automaton
   | S1 ->
       local s in
       do der s = 1.0 init last x and x = s and z = up(x -. 10.0)
       until z then S2 done
   | S2 ->
       local s in
       do der s = -1.0 init last x and x = s and z = up(-. (x +. 10.0))
       until z then S1 done
   end

let hybrid main_with_stops () =
  let { v = o; change = z } = k_with_stops () in
  let () = 
    (let x = print_float o in print_newline ()) every (period (0.1)) init () in
  ()
*)

(*
let node i j = x where
  rec lx = pre(x)
  and match j with
  | true -> do x = 1 and last_x = 0 -> lx done
  | false -> do last_x = 2 -> last x and x = last_x done
  end

let node h () = x where init x = 1

let node l () = x where rec last_x = 1 -> last x and x = last_x

let hybrid g () = x where init x = 1.0

let hybrid f () = x where
  init x = 1.0
  and
  automaton
  | S1 -> do done
  end
*)
