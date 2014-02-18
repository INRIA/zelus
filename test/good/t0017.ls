
let hybrid f(x) =
  let rec
      match x with
      | true -> do der y = 1.0 done
      | false -> do der y = 2.0 done
  and init y = 0.0 in
  y

(* commentaire *)
let hybrid g(x) =
  let rec y = up(x) in
  y

let hybrid main () =
  let _ = g (3.0) in
  ()

