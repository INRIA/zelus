let hybrid iplus (x, y) =
  let rec der xi = x +. yi init 0.0
  and der yi = y init 0.0
  in
  (xi, yi)

(* commentaire *)
let hybrid f(x) =
  let rec der m = x init 0.0 and der z = m init 1.0 and k = z and l = up(x) in
  let (r1, r2) = iplus(m, z) in
  iplus(r1, r2)

let hybrid main() =
  let (xi, yi) = f 2.0 in
  (*
  print_float xi;
  print_string "\t";
  print_float yi;
  print_newline ()
  *)
  ()

