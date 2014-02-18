(* TEST[-check 20 -period] ARGS[-precisetime] *)
(* Transition condition defined in parallel with automaton *)
(* For more information, add these two options to ARGS[] above:
      -lzeroc -lgcalls *)

let max = 2.0

let hybrid f z = pos where
  rec init pos = 0.0
  and automaton
    | S0 ->
        do
          der pos = 0.0
        until (z on (not atmax)) then S1
        done

    | S1 ->
        do
          der pos = 1.0
        until (up(pos -. max)) then S0
        done

  and atmax = (last pos >= max)
  (* 20120404: the program compiles if the last is removed, but the results are
               incorrect due to a scheduling bug. *)

let hybrid main () = check where
  rec z = period (1.0)
  and y = f(z)
  and check = present z -> (y <= max +. 0.1) else true

