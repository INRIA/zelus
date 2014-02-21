(*
On se débrouille, via la programmation, pour résoudre les problèmes
liés à la simulation, essentiellement :
- décollage de 0
- dépassement/inversion
Voir les commentaires ...
N.B. tout ça est valable en -sundialsI, moins bogué que le zc standard
*)

let left  = -1.
let right =  1.


let d1 = 0.0
let w1 = 1.0

(* si la bille n'est pas collée au mur pas de pb... *)
(* let d2 = 0.5 *)
(* bille collée : on a un système à 3 transitions
discrète qu'il faut détecter correctement ... *)
let d2 = right

let w2 = 0.0

let becomes x = if x then 1. else -.1.

let hybrid billiard1d ((d1, w1), (d2, w2)) =
  let
        rec der x1 = v1 init d1
        and der x2 = v2 init d2
        and der v1 = 0.0 init w1
        and der v2 = 0.0 init w2
        and present
        |       hit ->
        do
                v1 = last v2 and v2 = last v1
(* magouille 1 :
choc x1/x2 -> l'invariant x1 <= x2 peut être violé on corrige
"sioux", en tenant compte de l'immobilité éventuelle des billes
*)
                and x1 = if last v1 <> 0.0 then last x2 else last x1
                and x2 = if last v2 <> 0.0 then last x1 else last x2
        done
        |       hit2 -> do v2 = -. last v2 done
        |       hit1 -> do v1 = -. last v1 done
(* magouille 2 :
à cause de la magouille 1, on a un cycle qu'il faut briser avec des last...
*)
        and hit = up(last x1 -. last x2)
(* magouille 3 :
on teste les décollages de zéro
*)
        and hit2 = up(becomes(x2 > right))
        and hit1 = up(becomes(left > x1))
  in
  ((x1, v1), (x2, v2))

(* ** plotting ** *)

open Scope

let node plot (t, (x1, v1), (x2, v2)) =
  let s1 = scope2 (left -. 0.1, right +. 0.1,
                ("x1", linear, x1),
                ("x2", linear, x2)
        )
  and s2 = scope2 (-. max(w1, w2), max(w1, w2),
             ("v1", discrete false, v1), ("v2", discrete false, v2))
  in
  window2 ("doityourself", 8.0, t, s1, s2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and ((x1, v1), (x2, v2)) =
    billiard1d ((d1, w1), (d2, w2))
  in present
     | (period (0.07)) -> plot (t,(x1, v1), (x2, v2))
     else ()

