(* TEST[-check 1000] ARGS[-precisetime] *)
(* (Near-) simultaneous zero-crossings *)

let node count () = c where
  rec c = 0 fby c + 1

let node show_counter (n, c) =
  let () = print_string n in
  let () = print_string "=" in
  let () = print_int c in
  let () = print_newline () in
  ()

let ratio = 10.0

let hybrid main () =    (c1 / truncate(ratio) = c2)
                     || ((c1 + 1) / truncate (ratio) = c2)
 where rec
    der x1 = 1.0 init -1.0 reset z1 -> -1.0
 and
    z1 = up(x1)
 and
    c1 = present z1 -> count() init 0
 and
    () = present z1 -> show_counter ("c1", c1) else ()
 and
    der x2 = 1.0 init (-. ratio) reset z2 -> (-. ratio)
 and
    z2 = up(x2)
 and
    c2 = present z2 -> count() init 0
 and
    () = present z2 -> show_counter ("c2", c2) else ()

