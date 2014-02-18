(* TEST[-check 5] ARGS[] *)
(* Compilation of nested fbys. Expect to see 1, 2, 2, 2, 2, 2, ... *)

let node df () =
  let next_t =
    let rec p = 2 fby p in
    let result = 1 fby p in
    result in
  let () = print_int next_t in
  let () = print_newline () in
  next_t

let node main () = (y = 1) -> (y = 2) where
  y = df ()

