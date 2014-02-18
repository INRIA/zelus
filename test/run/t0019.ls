(* TEST[-check 8] ARGS[-avoidreinit -sundialsI -debugz] *)
(* Test detection of close but ordered zero-crossings; try to trigger sundials
   bug in CVRcheck1 by resetting x to exactly 0.0 after the first zero-crossing. *)

(*
  Different tests:

  with reinit:
  * for sundials: ARGS[-sundials]
  * for illinois: ARGS[-sundialsI -debugz]

  without reinit:
  * for sundials: ARGS[-sundials -avoidreinit]
  * for illinois: ARGS[-sundialsI -avoidreinit -debugz]

  logged output:
  * add -precisetime to ARGS to display the log with more precision.

  precision:
  * change the value of epsilon
    (On a 32-bit machine a value of -. 0.9e-14 should be sufficient to
     distinguish -sundials (with error) from -sundialsI (no error).)

  One of three output sequences can be observed:

  1. Correct detection: first zx, then zy

      I : 0.000000000000000e+00 -1.000000000000001e+01  -1.000000000000000e+01
      H : 0.000000000000000e+00    horizon=inf
      C': 9.999999999999991e+00 -1.268776750329437e-14   1.523087211907637e-15
zx->  Z : 9.999999999999991e+00  0   1
      D.: 9.999999999999991e+00 -1.268776750329437e-14   0.000000000000000e+00
      H : 9.999999999999991e+00    horizon=inf
      D : 9.999999999999991e+00 -1.268776750329437e-14   0.000000000000000e+00
      H : 9.999999999999991e+00    horizon=inf (reinit)
      C': 1.000000000000001e+01  1.139678863874588e-15   1.382744636716896e-14
zy->  Z : 1.000000000000001e+01  1   0
      D.: 1.000000000000001e+01  1.139678863874588e-15   1.382744636716896e-14
      H : 1.000000000000001e+01    horizon=inf
      D : 1.000000000000001e+01  1.139678863874588e-15   1.382744636716896e-14
      H : 1.000000000000001e+01    horizon=inf (reinit)
      C : 1.100000000000000e+02  9.999999999999997e+01   9.999999999999997e+01
      C : 2.100000000000000e+02  2.000000000000000e+02   2.000000000000000e+02

  2. Insufficient precision: detect xz and zy simultaneously.

      I : 0.000000000000000e+00 -1.000000000000001e+01  -1.000000000000000e+01
      H : 0.000000000000000e+00    horizon=inf
      C': 1.000000000000000e+01  1.200428645375951e-15   8.305856002976952e-15
zx+zy Z : 1.000000000000000e+01  1   1
      D.: 1.000000000000000e+01  1.200428645375951e-15   8.305856002976952e-15
      H : 1.000000000000000e+01    horizon=inf

  3. Bug in Sundials: detect zx, miss zy completely.

      I : 0.000000e+00  -1.000000e+01 -1.000000e+01
      H : 0.000000e+00   horizon=inf
      C': 1.000000e+01  -5.904999e-15  8.305856e-15
zx->  Z : 1.000000e+01   0   1
      D.: 1.000000e+01  -5.904999e-15  0.000000e+00
      H : 1.000000e+01   horizon=inf
      D : 1.000000e+01  -5.904999e-15  0.000000e+00
      H : 1.000000e+01   horizon=inf (reinit)
      C : 1.100000e+02   1.000000e+02  1.000000e+02
      C : 2.100000e+02   2.000000e+02  2.000000e+02
      C : 3.100000e+02   3.000000e+02  3.000000e+02
      C : 4.100000e+02   4.000000e+02  4.000000e+02
      C : 5.100000e+02   5.000000e+02  5.000000e+02
*)

let epsilon = -. 0.99e-14

let hybrid main () = first_x & then_y where
  rec der x = 1.0 init -10.0 reset zx -> 0.0
  and der y = 1.0 init (-10.0 +. epsilon)

  and zx = up(x)
  and zy = up(y)

  and sx = present zx -> true init false
  and sy = present zy -> true init false

  and first_x = present (zx on sy) -> false init true
  and then_y  = present (zy on (not sx)) -> false init true

