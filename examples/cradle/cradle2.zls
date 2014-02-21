
(*
works fine as long as positions are exchanged,
to avoid p0 to become greater than p1
*)

let pi = 3.1416
(* let mp6 = -. (pi /. 6.) *)
let mp6 = -. 0.5
let g = 9.80665
let l = 0.2

let pinit0 = mp6
let pinit1 = 0.
(* -. mp6 *)

let acc x = -. g /. l *. (sin x)

(* Main entry point *)
let hybrid cradle () =
  let
  rec der p0 = v0 init pinit0 reset hit01 -> last p1
  and der v0 = acc ( p0) init 0.0 reset hit01 -> last v1
  and der p1 = v1 init pinit1 reset hit01 -> last p0
  and der v1 = acc (p1) init 0.0 reset hit01 -> last v0
  and hit01 = up (last p0 -. last p1)

  and h = present hit01 -> -1.0 *. last h init -0.1
  (* and h = present hit01 -> 0.1 +. last h init -1. *)

  in h, (p0, v0 /. 10.) , (p1, v1 /. 10.)


let hybrid main () =
  let der t = 1.0 init 0.0 in
  let h, (p0, v0) , (p1, v1) = cradle () in
  present (period (0.05)) ->
      let s = Scope.scope4 (-1.0, 1.0,
                        ("p0", Scope.linear, p0),
                        ("h", Scope.linear, h-.0.7),
                        ("p1", Scope.linear, p1),
         ("v0", Scope.linear, v0)
        )
      in Scope.window ("cradle2", 3.0, t, s)
  else ()

