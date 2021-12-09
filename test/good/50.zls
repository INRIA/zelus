(*
  Test of dead code elimination.
  The print_int should be kept because it is an unsafe function.
  But the case is tricky because there is no variable on the LHS (rather the
  unit constant).
  A failure in this test is not detected by the Makefile, but can be seen
  by manual inspection of the resulting ml (is there a print_int or not?).
 *)
let node fd () =
  let rec y = 1 + 2
  and () = print_int y in
  3

let hybrid model () =
  let x = present (period (1.0)) -> fd () init 0 in
  ()

