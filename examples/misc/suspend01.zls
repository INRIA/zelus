
type risefall = Rising | Falling

let hybrid sawtooth () = y where
  rec init mode = Rising
  and init y = 0.0
  and present
      | (up(y -. 1.0))    -> do mode = Falling done
      | (up(-. y -. 1.0)) -> do mode = Rising  done
  and match mode with
      | Rising  -> do der y =    1.0 done
      | Falling -> do der y = -. 1.0 done
    
let hybrid sawtooth2 () = y where
  rec init rate = 1.0
  and present
      | (up(y -. 1.0))    -> do rate = -. 1.0 done
      | (up(-. y -. 1.0)) -> do rate =    1.0 done
  and der y = rate init 0.0

(* ** plotting ** *)
open Scope

let sample_period = 0.03

let hybrid timer v = z where
  rec der c = 1.0 init -. v reset z -> -. v
  and z = up(last c)

let node plot (t, x) =
  let s1 = scope (-2.0, 2.0, ("interpolated", linear, x)) in
  let s2 = scope (-2.0, 2.0, ("samples", points false, x)) in
  window2 ("suspend01", 8.0, t, s1, s2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and s = sawtooth () in
  present (timer sample_period) -> plot (t, s);
  ()

