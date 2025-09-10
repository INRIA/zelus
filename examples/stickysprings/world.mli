
type t

(* [world = init p1_initial p2_initial] *)
val create : float -> float -> t

(* [update world p1' p2'] *)
val update: t -> float -> float -> unit

