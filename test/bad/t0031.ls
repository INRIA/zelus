(*
   This program should be rejected because print_endline is an unsafe function
   (it has side effects) called from a continuous context.
 *)

let hybrid main () =
  let () = print_endline "not ok!" in
  ()

