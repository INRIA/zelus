(*
 *
 * Defines implicit function f : x |--> y such that g(x,y)=0
 *
 *)

val implicit1 :
  ((Dual.t -> Dual.t) -> float -> float) (* solver *) ->
  (Dual.t -> Dual.t -> Dual.t) (* constraint g(x,y)=0 *) -> Dual.t (* x *) -> Dual.t (* y0 *) -> Dual.t (* y *)

(*
 *
 * Defines implicit function f : (x,y) |--> z such that g(x,y,z)=0
 *
 *)

val implicit2 :
  ((Dual.t -> Dual.t) -> float -> float) (* solver *) ->
  (Dual.t -> Dual.t -> Dual.t -> Dual.t) (* constraint g(x,y,z)=0 *) ->
  Dual.t (* x *) -> Dual.t (* y *) -> Dual.t (* z0 *) -> Dual.t (* z *)
