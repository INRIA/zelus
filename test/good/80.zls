(* test of "on" in signal patterns *)
let sigon (s, b) = o where
  present
  | s() -> do
             match b with
             | true  -> do emit o done
             | false -> do done
           done

let hybrid f(x, y) = present x(1) on y -> 1

(*
let hybrid bouncing(y0,y'0) = y where
  rec der y = y' init y0
  and der y' = -.9.81 init y'0 reset o
  and o = present up(-. y) -> 0.8 *. y'
*)
