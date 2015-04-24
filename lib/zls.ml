
open Bigarray

(* Interfaces functions from within Zelus *)

type carray = (float, float64_elt, c_layout) Array1.t
type zarray = (int32, int32_elt,   c_layout) Array1.t

let cmake = Array1.create float64 c_layout
let zmake n =
  let r = Array1.create int32 c_layout n in
  Array1.fill r 0l;
  r

let length = Array1.dim

let get = Array1.get
let set = Array1.set
let get_zin v i = Array1.get v i <> 0l
let zero_fill r = Array1.fill r 0.0

type 's f_alloc = unit -> 's
type 's f_csize = 's -> int
type 's f_zsize = 's -> int
type 's f_maxsize = 's -> int * int
type 's f_ders = 's -> carray -> carray -> float -> int
type ('s, 'o) f_step = 's -> carray -> carray -> zarray -> float -> 'o * float
type 's f_zero = 's -> carray -> carray -> float -> int
type 's f_reset = 's -> carray -> unit

(* TODO: eliminate this ? *)
(* Compare two floats for equality, see:
 * http://www.cygnus-software.com/papers/comparingfloats/comparingfloats.htm *)
let time_eq f1 f2 =
  if abs_float (f1 -. f2) < min_float
  then true (* absolute error check for numbers around to zero *)
  else
    let rel_error =
      if abs_float f1 > abs_float f2
      then abs_float ((f1 -. f2) /. f1)
      else abs_float ((f1 -. f2) /. f2)
    in
    (rel_error <= 0.000001)
    (* Compare times with 99.9999% accuracy. *)

let time_leq t1 t2 = t1 < t2 || time_eq t1 t2
let time_geq t1 t2 = t1 > t2 || time_eq t1 t2

(* TODO:
   - adapt to the new sundials interface, rework, and simplify.
   - take advantage of the final field.
 *)

module type STATE_SOLVER =
  sig

    (* A session with the solver. *)
    type t

    type nvec
    val cmake : int -> nvec
    val unvec : nvec -> carray

    type rhsfn = float -> carray -> carray -> unit
    type dkyfn = nvec -> float -> int -> unit

    (* [init f c] creates a solver session from a function [f] and an initial
       state vector [c]. *)
    val initialize : rhsfn -> nvec -> t

    (* [reinit s t c] reinitializes the solver with the given time [t] and
       vector of continuous states [c]. *)
    val reinitialize : t -> float -> nvec -> unit

    (* [t' = step s tl c] given a state vector [c], takes a step to the next
       'mesh-point', or the given time limit [tl] (whichever is sooner). *)
    val step : t -> float -> nvec -> float

    (* [get_dky s t k c] for any time [t] since the last mesh-point, or initial
       instant, put [k]th derivatives into [c]. *)
    val get_dky : t -> dkyfn

    (* generic solver parameters *)
    val set_stop_time  : t -> float -> unit
    val set_min_step   : t -> float -> unit
    val set_max_step   : t -> float -> unit
    val set_tolerances : t -> float -> float -> unit
  end

module type ZEROC_SOLVER =
  sig
    (* A session with the solver *)
    type t

    type zcfn  = float -> carray -> carray -> unit

    val initialize   : int -> zcfn -> carray -> t
    val reinitialize : t -> float -> carray -> unit

    val step         : t -> float -> carray -> unit

    val has_roots    : t -> bool

    (* In [t = find s (f, c) zin], the get_dky function [f] must update the
       given array [c]. *)
    val find         : t -> ((float -> int -> unit) * carray) -> zarray -> float
  end

(* TODO : use this to create RUNTIMEs *)
module type ZELUS_PROG =
sig
  type state

  val alloc   : unit -> state
  val csize   : state -> int
  val zsize   : state -> int
  val maxsize : state -> int * int
  val ders    : state -> carray -> carray -> float -> int
  val step    : state -> carray -> carray -> zarray -> float -> float
  val zero    : state -> carray -> carray -> float -> int
  val reset   : state -> carray -> unit
end

module type RUNTIME =
sig
  val go : 's f_alloc
           * 's f_csize
           * 's f_zsize
           * 's f_maxsize
           * 's f_ders
           * ('s, 'o) f_step
           * 's f_zero
           * 's f_reset
           -> unit

  val check : 's f_alloc
              * 's f_csize
              * 's f_zsize
              * 's f_maxsize
              * 's f_ders
              * ('s, bool) f_step
              * 's f_zero
              * 's f_reset
              -> int
              -> unit
end

