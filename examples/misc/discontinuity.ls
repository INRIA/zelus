
let thresh1 = 0.987
let thresh2 = 1.987


let hybrid f () =
  let rec der t = 1.0 init 0.0
  and o1 = present (up (t -. thresh1)) -> 1.0 else 0.0
  and o2 = present (up (t -. thresh2)) -> 1.0 else 0.0 in
  t, o1, o2

let hybrid main () =
  let (r, o1, o2) = f () in
  present
    (period (0.6)) ->
       let rec t = 0.0 fby t +. 0.6 in
       let s1 = Scope.scope (-1.0, 5.0, ("r = ", Scope.linear, r))
       and s2 = Scope.scope (-1.0, 5.0, ("o1 =", Scope.linear, o1))
       and s3 = Scope.scope (-1.0, 5.0, ("o2 =", Scope.linear, o2))
       in Scope.window3 ("discontinuity", 8.0, t, s1, s2, s3)
  else ()

