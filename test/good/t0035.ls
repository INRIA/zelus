(* HSCC Example 2 *)
let discrete sgn x = 
  if x < 0.0 then -1.0
  else if x > 0.0 then 1.0
  else 0.0

let hybrid main () =
  let y_0 = -. 1.0 in
  let rec der x = 0.0 init -. sgn(y_0) reset | (up(y)) -> -. 1.0 | (up(-. y)) -> 1.0
  and der y = x init y_0 in
  ()

