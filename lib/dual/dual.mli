(*
 *
 * Dual numbers
 *
 * This module can be used for automatic differentiation and
 * the computation of Jacobians.
 *
 *)

type t

val make : float -> float -> t

val make_re : float -> t
val make_im : float -> t

val const : float -> t
val disc : float -> t

val re : t -> float
val im : t -> float

val set_re : t -> float -> unit
val set_im : t -> float -> unit

val (+.) : t -> t -> t
val (-.) : t -> t -> t
val (~-.) : t -> t
val ( *. ) : t -> t -> t
val (/.) : t -> t -> t
val inv : t -> t

val sqrt : t -> t
val exp : t -> t
val log : t -> t
val log10 : t -> t

val ( ** ) : t -> t -> t

val cos : t -> t
val sin : t -> t
val tan : t -> t 

val acos : t -> t
val asin : t -> t
val atan : t -> t 

val atan2 : t -> t -> t

val cosh : t -> t
val sinh : t -> t
val tanh : t -> t 

val ceil : t -> t
val floor : t -> t
val abs_float : t -> t
val mod_float : t -> t -> t
val frexp : t -> (t*int)
val ldexp : t -> int -> t
val modf : t -> (t*t)

val float : int -> t
val float_of_int : int -> t

val truncate : t -> int
val int_of_float : t -> int

val infinity : t
val neg_infinity : t
val nan : t
val max_float : t
val min_float : t
val epsilon_float : t
val classify_float : t -> Pervasives.fpclass

val compare : t -> t -> int
val hash : t -> int

val (>.) : t -> t -> bool
val (<.) : t -> t -> bool
val (=.) : t -> t -> bool
val (>=.) : t -> t -> bool
val (<=.) : t -> t -> bool
val (<>.) : t -> t -> bool

val string_of_float : t -> string
val float_of_string : string -> t

val print_float : t -> unit
val prerr_float : t -> unit

val read_float : unit -> t

val string_of_dual : t -> string
