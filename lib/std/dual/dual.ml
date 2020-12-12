(*
 *
 * Dual numbers
 *
 * This module can be used for automatic differentiation and
 * the computation of Jacobians.
 *
 *)

type t

(* val compare : t -> t -> int *)

external compare : t -> t -> int = "dual__compare__ml"

(* val make : float -> float -> t *)

external make : float -> float -> t = "dual__make__ml"

(* val zero : t *)

let zero = make 0. 0.

(* val make_real : float -> t *)

let make_re x = make x 0.

(* val make_der : float -> t *)

let make_im x' = make 0. x'

(* val const : float -> t *)

let const x = make x 0.

(* val disc : float -> t *)

let disc x = make x Pervasives.nan

(* val real : t -> float *)

external re : t -> float = "dual__re__ml"

(* val der : t -> float *)

external im : t -> float = "dual__im__ml"

(* val set_re : t -> float -> unit *)

external set_re : t -> float -> unit = "dual__set_re__ml"

(* val set_im : t -> float -> unit *)

external set_im : t -> float -> unit = "dual__set_im__ml"

(* val hash : t -> int *)

let mult_factor = Pervasives.float_of_int (Pervasives.max_int / 2)

let hash x =
  let y = re x in
  let z = Pervasives.abs_float y
  and s = Pervasives.compare y 0. in
  let e = Pervasives.floor (Pervasives.log10 z) in
  let m = Pervasives.truncate (mult_factor *. z /. (10. ** e)) in
    s * (m + (Pervasives.truncate e))

(* Generic non continuous operator *)

let apply_disc foo x = make (foo (re x)) Pervasives.nan

(* val add : t -> t -> t *)

external (+.) : t -> t -> t = "dual__add__ml"

(* val sub : t -> t -> t *)

external (-.) : t -> t -> t = "dual__sub__ml"

(* val minus : t -> t *)

external (~-.) : t -> t = "dual__minus__ml"

(* val ( *. ) : t -> t -> t *)

external ( *. ) : t -> t -> t = "dual__mpy__ml"

(* val inv : t -> t *)

external inv : t -> t = "dual__inv__ml"

(* val div : t -> t -> t *)

external (/.) : t -> t -> t = "dual__div__ml"

(* val sqrt : t -> t *)

external sqrt : t -> t = "dual__sqrt__ml"

(* val exp : t -> t *)

external exp : t -> t = "dual__exp__ml"

(* val log : t -> t *)

external log : t -> t = "dual__log__ml"

(* val log10 : t -> t *)

let log10 _ = failwith "Dual.log10: not implemented"

(* val ( ** ) : t -> t -> t *)

let ( ** ) _ _ = failwith "Dual.( ** ): not implemented"

(* val cos : t -> t *)

external cos : t -> t = "dual__cos__ml"

(* val sin : t -> t *)

external sin : t -> t = "dual__sin__ml"

(* val tan : t -> t *)

external tan : t -> t = "dual__tan__ml"

(* val acos : t -> t *)

let acos _ = failwith "Dual.acos: not implemented"

(* val asin : t -> t *)

let asin _ = failwith "Dual.afin: not implemented"

(* val atan : t -> t *)

let atan _ = failwith "Dual.atan: not implemented"

(* val atan2 : t -> t -> t *)

let atan2 _ _ = failwith "Dual.atan2: not implemented"

(* val cosh : t -> t *)

let cosh _ = failwith "Dual.cosh: not implemented"

(* val sinh : t -> t *)

let sinh _ = failwith "Dual.sinh: not implemented"

(* val tanh : t -> t  *)

let tanh _ = failwith "Dual.tanh: not implemented"

(* val ceil : t -> t *)

let ceil x = apply_disc Pervasives.ceil x

(* val floor : t -> t *)

let floor x = apply_disc Pervasives.floor x

(* val abs_float : t -> t *)

let abs_float x =
  let c = compare x zero in
    if c > 0
    then x
    else if c < 0
    then ~-. x
    else make 0. Pervasives.nan

(* val mod_float : t -> t -> t *)

let mod_float _ _ = failwith "Dual.mod_float: not implemented"

(* val frexp : t -> (t*int) *)

let frexp _ = failwith "Dual.frexp: not implemented"

(* val ldexp : t -> int -> t *)

let ldexp _ _ = failwith "Dual.ldexp: not implemented"

(* val modf : t -> (t*t) *)

let modf _ = failwith "Dual.modf: not implemented"

(* val float : int -> t *)

let float n = make (Pervasives.float n) 0.

(* val float_of_int : int -> t *)

let float_of_int n = make (Pervasives.float_of_int n) 0.

(* val truncate : t -> int *)

let truncate x = Pervasives.truncate (re x)

(* val int_of_float : t -> int *)

let int_of_float x = Pervasives.int_of_float (re x)

(* val infinity : t *)

let infinity = make Pervasives.infinity 0.

(* val neg_infinity : t *)

let neg_infinity = make Pervasives.neg_infinity 0.

(* val nan : t *)

let nan = make Pervasives.nan 0.

(* val max_float : t *)

let max_float = make Pervasives.max_float 0.

(* val min_float : t *)

let min_float = make Pervasives.min_float 0.

(* val epsilon_float : t *)

let epsilon_float = make Pervasives.epsilon_float 0.

(* val classify_float : t -> Pervasives.fpclass *)

let classify_float x = Pervasives.classify_float (re x)

(* val gt : t -> t -> bool *)

let (<.) x y = (re x) < (re y)

(* val lt : t -> t -> bool *)

let (>.) x y = (re x) > (re y)

(* val eq : t -> t -> bool *)

let (=.) x y = (re x) = (re y)

(* val gte : t -> t -> bool *)

let (>=.) x y = (re x) >= (re y)

(* val lte : t -> t -> bool *)

let (<=.) x y = (re x) <= (re y)

(* val neq : t -> t -> bool *)

let (<>.) x y = (re x) <> (re y)

(* val string_of_float : t -> string *)

let string_of_float x = Pervasives.string_of_float (re x)

(* val float_of_string : string -> t *)

let float_of_string s = make (Pervasives.float_of_string s) 0.

(* val print_float : t -> unit *)

let print_float x = Pervasives.print_float (re x)

(* val prerr_float : t -> unit *)

let prerr_float x = Pervasives.prerr_float (re x)

(* val read_float : unit -> t *)

let read_float () = make_re (Pervasives.read_float ())

(* val string_of_dual : t -> string *)

let string_of_dual x =
  Printf.sprintf "%f+i%f" (re x) (im x)
