
open Ztypes
open Bigarray

(* Interfaces functions from within Zelus *)

type carray = (float, float64_elt, c_layout) Array1.t
type zarray = (int32, int32_elt,   c_layout) Array1.t

let cmake n =
  let r = Array1.create float64 c_layout n in
  Array1.fill r 0.0;
  r
		      
let zmake n =
  let r = Array1.create int32 c_layout n in
  Array1.fill r 0l;
  r

let length = Array1.dim

let get = Array1.get
let set = Array1.set
let get_zin v i = Array1.get v i <> 0l
(* fill zinvec with zeros *)
let zzero zinvec length =
  for i = 0 to length - 1 do
    Array1.set zinvec i 0l
  done
				      
type 's f_alloc = unit -> 's
type 's f_maxsize = 's -> int * int
type 's f_csize = 's -> int
type 's f_zsize = 's -> int
type ('s, 'o) f_step = 's -> carray -> carray -> zarray -> float -> 'o
type 's f_ders = 's -> carray -> carray -> zarray -> carray -> float -> unit
type 's f_zero = 's -> carray -> zarray -> carray -> float -> unit
type 's f_reset = 's -> unit
type 's f_horizon = 's -> float

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

    (* The type of vectors used internally by the solver. *)
    type nvec

    (* Create a vector of the given size. *)
    val cmake : int -> nvec

    (* Unwrap a vector returning an array of continuous-state values. *)
    val unvec : nvec -> carray

    (* A right-hand-side function called by the solver to calculate the
       instantaneous derivatives: [f t cvec dvec].
       - t, the current simulation time (input)
       - cvec, current values for continuous states (input)
       - dvec, the vector of instantaneous derivatives (output) *)
    type rhsfn = float -> carray -> carray -> unit

    (* An interpolation function: [df cvec t k]
       - cvec, a vector for storing the interpolated continuous states (output)
       - t, the time to interpolate at,
       - k, the derivative to interpolate *)
    type dkyfn = nvec -> float -> int -> unit

    (* [initialize f c] creates a solver session from a function [f] and
       an initial state vector [c]. *)
    val initialize : rhsfn -> nvec -> t

    (* [reinitialize s t c] reinitializes the solver with the given time
       [t] and vector of continuous states [c]. *)
    val reinitialize : t -> float -> nvec -> unit

    (* [t' = step s tl c] given a state vector [c], takes a step to the next
       'mesh-point', or the given time limit [tl] (whichever is sooner),
       updating [c]. *)
    val step : t -> float -> nvec -> float

    (* Returns an interpolation function that can produce results for any
       time [t] since the last mesh-point or the initial instant. *)
    val get_dky : t -> dkyfn

    (* generic solver parameters *)
    val set_stop_time  : t -> float -> unit
    val set_min_step   : t -> float -> unit
    val set_max_step   : t -> float -> unit
    val set_tolerances : t -> float -> float -> unit
  end

module type ZEROC_SOLVER =
  sig
    (* A session with the solver. A zero-crossing solver has two internal
       continuous-state vectors, called 'before' and 'now'. *)
    type t

    (* Zero-crossing function: [g t cvec zout]
       - t, simulation time (input)
       - cvec, vector of continuous states (input)
       - zout, values of zero-crossing expressions (output) *)
    type zcfn  = float -> carray -> carray -> unit

    (* Create a session with the zero-crossing solver:
       [initialize nroots g cvec0]
       - nroots, number of zero-crossing expressions
       - g, function to calculate zero-crossing expressions
       - cvec0, initial continuous state

       Sets the 'now' vector to cvec0. *)
    val initialize   : int -> zcfn -> carray -> t

    (* The same but does not run [g] at initialization time *)
    val initialize_only   : int -> zcfn -> carray -> t

    (* Reinitialize the zero-crossing solver after a discrete step that
       updates the continuous states directly: [reinitialize s t cvec].
       - s, a session with the zero-crossing solver
       - t, the current simultation time
       - cvec, the current continuous state vector

       Resets the 'now' vector to cvec. *)
    val reinitialize : t -> float -> carray -> unit

    (* Advance the zero-crossing solver after a continuous step:
       [step s t cvec].
       - s, a session with the zero-crossing solver
       - t, the current simultation time
       - cvec, the current continuous state vector

       Moves the current 'now' vector to 'before', then sets 'now' to cvec. *)
    val step         : t -> float -> carray -> unit

    val takeoff      : t -> bool
    (* Returns true if one zero-crossing signal moves from 0 to v > 0 *)
    (* Compares the 'before' and 'now' vectors and returns true only if
       there exists an i, such that before[i] < 0 and now[i] >= 0. *)
    val has_roots    : t -> bool

    (* Locates the time of the zero-crossing closest to the 'before' vector.
       Call after [has_roots] indicates the existence of a zero-crossing:
       [t = find s (f, c) zin].
       - The [get_dky] function [f] is provided by the state solver and is
         expected to update the array [c] with the interpolated state.
       - zin, is populated with the status of all zero-crossings
       - the returned values is the simulation time of the earliest
         zero-crossing that was found. *)
    val find         : t -> ((float -> int -> unit) * carray) -> zarray -> float
  end

module type RUNTIME =
sig
  val go : unit hsimu -> unit
  val check : bool hsimu -> int -> unit
end

module type DISCRETE_RUNTIME =
sig
  val go : float -> (unit -> unit) -> unit
end

