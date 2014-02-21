(*
Met en évidence plusieurs problèmes :

- le décollage de 0 ne peut pas être détecté comme une racine 
- quelques pistes :
  * détecter les décollages avec une méthode ad hoc (à définir !)
  * utiliser un détecteur standard avec :
    - se débrouiller pour les fonctions de zc soient à -eps
    - fabriquer des fonctions de zc discontinues, e.g. 
      if (x <= 0) then -1 else 1
      n.b. le zc standard étant normalement équivalent à :
      if (x < 0) then -1 else 1

On explore ici la solution "triche" qu consiste à ajouter des eps

N.B. Cette expérience met en lumière des bugs (en tout cas des faiblesses)
de la détection de zero-crossing pas sundials, tous les exemples 
du cas 2 fonctionnent avec l'option -sundialsI
*)

let left  = -1.
let right =  1.

(*
CAS 1, NE PEUT PAS MARCHER :
d2 collée -> qq soit la vitesse, pas de zero-crossing :
- b1 stoppe à mur +e
- b2 prend la vitesse last v1, traverse SANS z-c (car part de 0.0)
      et part à l'infini
*)
(* let eps = 0.0 let w1 = 1.0 *)

(*
CAS 2.a) Marchotte ...
d2 décollée et vitesse "raisonable" vis-à-vis de eps -> ok 
*)
(* let eps = 0.00001  let w1 = 1.0 *)

(*
CAS 2.b) Limite du 2.a :
d2 décollée et vitesse trop rapide vis-à-vis de eps :
- des cas de ratage de mur 
- des cas d'inversion

N.B.i ça semble lié à la détection de zc dans sundials,
avec -sundialsI, tout marche correctement ...
*)
(* let eps = 0.0000001  let w1 = 1.0 *)
(* let eps = 0.00000000000000001  let w1 = 2.0 *)
(* let eps = 0.00001  let w1 = 1.0 *)
(* let eps = 0.0000001  let w1 = 3.0 *)
let eps = 0.00000001  let w1 = 10.0

let d1 = 0.0
let d2 = right -. eps

let w2 = 0.0

let hybrid billiard1d ((d1, w1), (d2, w2)) =
  let
        rec der x1 = v1 init d1
        and der x2 = v2 init d2
        and der v1 = 0.0 init w1
        and der v2 = 0.0 init w2
        and present
        |       hit -> do v1 = last v2 and v2 = last v1 done
        |       hit2 -> do v2 = -. last v2 done
        |       hit1 -> do v1 = -. last v1 done
        and hit = up(x1 -. x2)
        and hit2 = up(x2 -. right) 
        and hit1 = up(left -. x1)
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
  window2 ("problems", 8.0, t, s1, s2)

(* ** main ** *)

let hybrid main () = let
  rec der t = 1.0 init 0.0
  and ((x1, v1), (x2, v2)) =
    billiard1d ((d1, w1), (d2, w2))
  in present
     | (period (0.1)) -> plot (t,(x1, v1), (x2, v2))
     else ()

