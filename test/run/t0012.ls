(* TEST[-check 20 -period] ARGS[-precisetime] *)
(* Combination: init, p-state, c-variable = function *)
(* For more information, add these two options to ARGS[] above:
      -lzeroc -lgcalls *)

let hybrid integr(x', x0) = x where rec der x = x' init x0

let hybrid avoidance x_i = x where
  rec init x = x_i
  and automaton
      | S0 -> do until (init on true) then S1(x) done

      | S1(x0) ->
          do
            x = integr(x', x0)
          done

  and x' = 1.0

open Basics

let hybrid main () = check where
  rec y = avoidance(-2.0)
  and der t = 1.0 init -2.0
  and check = (t =~= y)
  and p = period (1.0)

