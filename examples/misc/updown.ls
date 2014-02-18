(* The hybrid version of the two state automaton "up/down" *)
(* from Florence Maraninchi, ESOP'98 *)

let hybrid f () = y where
  rec init y = 0.0
  and automaton
      | S1 -> do der y = 1.0 until (up(y -. 10.0)) then S2
      | S2 -> do der y = -1.0 until (up(-. y -. 10.0)) then S1
      end

let hybrid g () = y where
  rec init y = 0.0
  and automaton
      | S1 -> 
          do der y = 1.0 until (up(last y -. 10.0))
          then do y = last y +. 1.0 in S2
      | S2 -> 
          do der y = -1.0 until (up(-. last y -. 10.0)) 
          then do y = last y -. 1.0 in S1
      end

(*
let hybrid h () = y where
  rec automaton
      | S1(y0) -> 
          do der y = 1.0 init y0 until (up(last y -. 10.0))
          then S2(y +. 1.0) done
      | S2(y0) -> 
          do der y = -1.0 init y0 until (up(-. last y -. 10.0)) 
          then S2(y -. 1.0) done
      init S1(0.0)
*)

let hybrid i () = y where
  rec init y = 0.0
  and automaton
      | S1 -> 
          local z in
          do der y = 1.0 reset z -> last y +. 1.0
          and z = up(last y -. 10.0)
          until z then S2
      | S2 -> 
          local z in
          do der y = -1.0 reset z -> last y -. 1.0
          and z = up(-. last y -. 10.0) 
          until z then S1
      end

let hybrid f_at_zero () = y where
  rec init y = -1.0
  and automaton
      | S1 -> do der y = 1.0 until (up(y)) then S2
      | S2 -> do der y = -1.0 until (up(-. y)) then S1
      end

(* The main function *)
let hybrid main () =
  let der t = 1.0 init 0.0 in
  let y = f_at_zero () in
  present (period (0.1)) ->
      (let s = Scope.scope (-12.0, 12.0, ("y", Scope.linear, y))
      in Scope.window ("updown", 60.0, t, s));
  ()
