(* TEST[-check 10000 -period] ARGS[-maxcstep 1.0 -precisetime] *)
(* An example where a zero-crossing is skipped in Sundials 2.4.0. *)
(* For more information, add these two options to ARGS[] above:
      -lzeroc -lgcalls *)

let hybrid main () = check where
  rec der x1 = 1.0 init -. 2.0
  and z1 = up(x1)

  and der timer = 1.0 init -. 0.50 reset tz -> -. 0.50
  and tz = up(timer)

  (* Put a zero-crossing expression to zero after the reset just before z1 is
     hit. This triggers a [CVODES WARNING]. *)
  and c = present tz -> last c + 1 init 0
  and z2 = up(if c = 3 then 0.0 else 1.0)

  (* This line is just for the testing framework. The experiment exhibits the
     same problem without it. The variable t can only be bigger than 0.0 if the
     tz zero-crossing is missed. *)
  and check = present (period (5.0)) -> (timer < 1.0) init true

