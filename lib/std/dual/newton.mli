(*
 *
 * Newton-Raphson method: solves g(x)=0 starting from x0
 * Returns x such that - eps <= g(x) <= eps
 * Raises Not_found whenever x, g(x) or d g(x) / dx becomes nan, infinity or neg_infinity
 * Raises Not_found if x goes out of interval [x0 -. radius; x0 +. radius]
 *
 *)

val solve : float -> float -> (Dual.t -> Dual.t) -> float -> float

(*
 *
 * Gauss-Newton method: solves g(x,y)=0 such that (x-x0)^2 + (y-y0)^2 is minimal
 * Returns (x,y) such that - eps <= g(x,y) <= eps
 * Raises Not_found whenever (x,y), g(x,y) or d g(x,y)/dx or dy becomes nan, infinity or neg_infinity
 * Raises Not_found if (x,y) goes out a the disc or a given radius centered on (x0,y0)
 *
 *)

val solve2 : float -> float -> (Dual.t -> Dual.t -> Dual.t) -> float -> float -> (float * float)
