(* The example of Benoit *)

let hybrid benoit1 () = y where
  rec der y = 2.0 *. sqrt (sqrt(y *. y)) init 0.0

let hybrid benoit () = y where
  rec der y = 2.0 *. sqrt (sqrt(y *. y)) init 1.0


(* This system has two solutions: y(t) = t and y(t) = t^2 *)

open Scope

let hybrid main () =
  let der t = 1.0 init 0.0 in
  let y = benoit () in
  present (period (0.1)) ->
      let s = Scope.scope2 (-1.0, 2.5, ("y", Scope.linear, y),
                                       ("sqrt y", Scope.linear, sqrt y))
      in Scope.window ("sincos", 10.0, t, s)
  else ()

