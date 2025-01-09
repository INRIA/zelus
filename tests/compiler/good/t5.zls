let hybrid iplus (x, y) =
  let der xi = x init 0.0
  and der yi = y init 0.0
  in
  (xi, yi)

(* commentaire *)
let hybrid f(x,y) =
  let rec der m = y init 0.0 and der z = m init 1.0 and k = z and l = up(m) in
  iplus (m, z)

let hybrid main () =
  let _ = f (3.0, 4.0) in
  ()

