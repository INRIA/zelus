(*
   This program should be rejected because last() is used on a continuous signal
   that is not directly the value of a continuous state. That is, the signal
   results from a calculation on one or more continuous states, and thus the
   "last x" cannot simply be replaced by a variable "lx" from the solver.
 *)

let hybrid main () = () where
  rec
      der t1 = 1.0 init 0.0
  and
      t2 = t1 +. 1.0
  and
      x = last t2

