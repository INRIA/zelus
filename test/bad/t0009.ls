(*
   This program should be rejected because although last() is used on a
   continuous signal coming directly from a continuous state, it is used in a
   context where the compiler cannot, in general, know this (and further more,
   there may be intermediate copies of the value). That is, the compiler cannot
   know which solver variable (the "lx") should be used to replace the
   expression "last t2".
 *)

let hybrid f () = t1 where
  der t1 = 1.0 init 0.0

let hybrid main () = () where
  rec
      t2 = f ()
  and
      x = last t2

