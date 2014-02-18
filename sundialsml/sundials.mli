(***********************************************************************)
(*                                                                     *)
(*              Ocaml interface to Sundials CVODE solver               *)
(*                                                                     *)
(*           Timothy Bourke (INRIA) and Marc Pouzet (LIENS)            *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

(** Generic definitions for the Sundials suite

 @version VERSION()
 @author Timothy Bourke (INRIA)
 @author Marc Pouzet (LIENS)
 *)

(** {2 Constants} *)

(** The BIG_REAL constant.
    @cvode <node5#s:types> Data Types
 *)
val big_real : float

(** The UNIT_ROUNDOFF constant.
    @cvode <node5#s:types> Data Types
 *)
val unit_roundoff : float

(** {2 Arrays of floats} *)

(** A {{:OCAML_DOC_ROOT(Bigarray.Array1)} (Bigarray)} vector of floats. *)
type real_array =
  (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array1.t

(** [make_real_array n] returns a {!real_array} with [n] elements. *)
val make_real_array : int -> real_array

(** A {{:OCAML_DOC_ROOT(Bigarray.Array2)} (Bigarray)} two-dimensional array of
   floats. *)
type real_array2 =
  (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t

(** [make_real_array2 m n] returns a {!real_array2} with [m] x [n]  elements. *)
val make_real_array2 : int -> int -> real_array2

(** Utility functions for serial nvectors as used in {!Cvode_serial}. *)
module Carray :
  sig
    type t = real_array

    (** An array with 0 elements. *)
    val empty : t

    (** [create n] returns an array with [n] elements. *)
    val create : int -> t

    (** Copies the contents of an {{:OCAML_DOC_ROOT(Array)} Array} into a
       {!real_array} *)
    val of_array : float array -> t

    (** Create a new array with the same contents as an existing one. *)
    val of_carray : t -> t

    (** [fill src dst] copies all elements of array [src] into array [dst]. They
        must both have the same length. *)
    val blit : t -> t -> unit

    (** [fill a c] sets all elements of the array [a] to the constant [c]. *)
    val fill : t -> float -> unit

    (** Returns the length of an array *)
    val length : t -> int

    (** [print_with_time t a] prints a line containing the current time (see
        {!print_time}) followed by a tab-delimited list of the values of [a],
        and then a newline. See also {!extra_precision}. *)
    val print_with_time : float -> t -> unit

    (** [app f a] applies [f] to the values of each element in [a]. *)
    val app : (float -> unit) -> t -> unit

    (** [app f a] applies [f] to the indexes and values of each element
        in [a]. *)
    val appi : (int -> float -> unit) -> t -> unit

    (** [map f a] applies [f] to the value of each element in [a] and
        stores the result back into the same element. *)
    val map : (float -> float) -> t -> unit

    (** [map f a] applies [f] to the index and value of each element
        in [a] and stores the result back into the same element. *)
    val mapi : (int -> float -> float) -> t -> unit
  end

(** {2 Arrays of ints} *)

(** A {{:OCAML_DOC_ROOT(Bigarray.Array1)} (Bigarray)} vector of integers. *)
type int_array =
  (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t

(** [make_int_array n] returns an {!int_array} with [n] elements. *)
val make_int_array  : int -> int_array

(** {2 Arrays of roots (zero-crossings)} *)

(** Utility functions for arrays of roots (zero-crossings). *)
module Roots :
  sig
    type t = int_array
    type val_array = Carray.t

    type root_event =
      | NoRoot      (** No root (0)       *)
      | Rising      (** Rising root (1)   *)
      | Falling     (** Falling root (-1) *)

    (** An array with 0 elements. *)
    val empty : t

    (** [create n] returns an array with [n] elements, each set to NoRoot. *)
    val create : int -> t

    (** Returns the length of an array *)
    val length : t -> int

    (** [print r] prints a line containing a tab-delimited list of the values of
        [r] (in the format "% d", where 0 = NoRoot, 1 = Rising,
        -1 = Falling), and then a newline. *)
    val print : t -> unit

    (** [get r i] returns [true] if the value of the [i]th element of [r] is
        either Rising or Falling. *)
    val get : t -> int -> bool

    (** [rising r i] returns [true] if the value of the [i]th element of [r] is
        Rising. *)
    val rising : t -> int -> bool

    (** [falling r i] returns [true] if the value of the [i]th element of [r] is
        Falling. *)
    val falling : t -> int -> bool

    (** [get r i] returns the value of the [i]th element of [r]. *)
    val get' : t -> int -> root_event

    (** [set r i v] sets the value of the [i]th element of [r]. *)
    val set : t -> int -> root_event -> unit

    (** [set r i v] sets the value of the [i]th element of [r] to Rising if v is
        true, and to NoRoot otherwise. *)
    val set_rising : t -> int -> bool -> unit

    (** [set r i v] sets the value of the [i]th element of [r] to Falling if v is
        true, and to NoRoot otherwise. *)
    val set_falling : t -> int -> bool -> unit

    (** Returns 0 for NoRoot, 1 for Rising, and -1 for Falling. *)
    val to_int : root_event -> int

    (** Returns NoRoot for 0, Rising for 1, and Falling for -1. *)
    val from_int : int -> root_event

    (** Resets all elements to NoRoot. *)
    val reset : t -> unit

    (** Returns [true] if any elements are equal to Rising or Falling. *)
    val exists : t -> bool

    (** [appi f r] applies [f] to the indexes and values of each element
        in [r]. *)
    val appi : (int -> root_event -> unit) -> t -> unit
  end

(** {2 Miscellaneous utility functions} *)

(** [print_time (s1, s2) t] prints [t] with [s1] on the left and [s2] on the
    right.  *)
val print_time : string * string -> float -> unit

(** Controls the precision of {!print_time} and {!Carray.print_with_time}.
 
    If [true] the format [%.15e] is used, otherwise [%e]
    (the default) is used. *)
val extra_precision : bool ref

(** [format_float fmt f] formats [f] according to the format string [fmt],
    using the low-level [caml_format_float] function. *)
val format_float : string -> float -> string

(** Equivalent to [format_float "%a"].
  
    [floata f] returns the bit-level representation of [f] in
    hexadecimal as a string. *)
val floata : float -> string

