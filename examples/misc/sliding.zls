let node count (x) = o where
  rec y = if x then 1 else 0
  and o = y -> pre o + y

let hybrid main1 () = (time, o) where
  rec der time = 1.0 init 0.0
  and o = (0.0 -> time +. last o) every true init 0.0

let hybrid f () = (x, y) where
  rec der x = y init -1.0
  and y = -1.0 every up(x) | 1.0 every up(-. x) init 1.0

let hybrid g(t) = (x, y) where
  rec
      automaton
      | Up -> do der x = -. t  +. 1.0  until z then Flat done
      | Flat -> do der x = 0.0 done
      end
  and init x = (-1.0 /. 2.0)
  and z = up(x)
  and
      y = 1.0 every up(x) init -1.0
  and
      der o = 1.0 init -1.0 and z1 = up(o)
  and
      der k = 1.0 init -2.0 and z2 = up(k)
  and
      der m = 1.0 init -1.0 reset -1.0 every up(m)

open Scope

let p = 1.0

(*
let hybrid timer p = z where
  rec der t = 1.0 init 0.0 reset 0.0 every z and z = up(t -. p)
 *)

let hybrid timer p = z where
  rec der t = 1.0 init -. p reset -. p every z and z = up(t)

let hybrid main () =
  let der t = 1.0 init 0.0 in
  let (x, y) = main1 () in
  let w = (
    let s1 = Scope.scope (-1.0, 10.0, ("x", Scope.points false, x))
    and s2 = Scope.scope (-1.5,  200.0, ("y", Scope.points true,  y))
    in Scope.window2 ("sliding", 10.0, t, s1, s2))
    every timer p init ()
  in
  w

