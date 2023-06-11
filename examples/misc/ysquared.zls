open Scope

let hybrid f () = (x1, x2, z) where
  rec der y = 5.0 init 0.0
  and x1 = y *. y
  and der x2 = 2.0 *. y *. 5.0 init 0.0
  and z = x1 -. x2

let p = 0.6

let hybrid main () =
  let (x1, x2, z) = f () in
  present
    (period (0.6)) ->
       let rec t = 0.0 fby t +. p in
       let s1 = Scope.scope (0.0, 50.0, ("x1 = y ** 2", Scope.linear, x1))
       and s2 = Scope.scope (0.0, 50.0, ("d/dt(x2) = 2 * y * dy/dt",
                                         Scope.linear, x2))
       and s3 = Scope.scope (0.0, 50.0, ("x1 - x2", Scope.linear, z))
       in Scope.window3 ("ysquared", 8.0, t, s1, s2, s3)
  else ()

