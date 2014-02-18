(* TEST[-check 20 -period] ARGS[-precisetime] *)
(* Test for resetting of derivatives in present (and, indirectly, also test the
   period construct). *)
(* For more information, add these two options to ARGS[] above:
      -lzeroc -lgcalls *)

open Basics

let node do_check (x) =
  let () = print_string "x=" in
  let () = print_float x in
  let () = print_string "\n" in
  let () = flush_all () in
  x =~= -1.5

(*
  Expected behaviour:

  t:  0.0   0.5     1.0        1.5    2.0     3.0       3.5     4.0      5.0

  x: -1.0  -0.5   0.0/-2.0    -1.5   -1.0   0.0/-2.0   -1.5    -1.0    0.0/-2.0

                                |                        |
                            check here               check here        ...etc.
 *)

let hybrid main () = check where
  rec present
    (z) -> do x = -2.0 done
    else do der x = 1.0 done
  and init x = -1.0
  and z = up(x +. 0.0)
  and check = present (period 1.5(2.0)) -> do_check x else true

