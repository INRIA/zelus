(*
   This program should be rejected because of the cycle [x --> y y --> x].
 *)

let hybrid main () = () where
  rec der x = 1. init 0. reset
    |  up(y) -> -1.
    |  up(-. y) -> -1.
  and der y = 1. init 0. reset up(x) -> -1.

(* 
   Note that the program is correctly rejected if we remove one of the
   zerocrossings on der x.
*)
