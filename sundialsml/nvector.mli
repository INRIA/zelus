(***********************************************************************)
(*                                                                     *)
(*              Ocaml interface to Sundials CVODE solver               *)
(*                                                                     *)
(*            Timothy Bourke (INRIA) and Marc Pouzet (LIENS)           *)
(*                                                                     *)
(*  Copyright 2013 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

(***********************************************************************)
(* Much of the comment text is taken directly from:                    *)
(*                                                                     *)
(*               User Documentation for CVODE v2.6.0                   *)
(*                Alan C. Hindmarsh and Radu Serban                    *)
(*              Center for Applied Scientific Computing                *)
(*              Lawrence Livermore National Laboratory                 *)
(*                                                                     *)
(***********************************************************************)

(** Define abstract NVectors using imperative or functional operations

  The Sundials solvers are written in a data-independent manner. They all
  operate on generic vectors through a set of operations defined by the
  particular {!nvector} implementation. The {!Cvode_nvector} module operates on
  abstract nvectors.

  The Ocaml interface provides two ways to define generic nvectors: either
  through a set of (imperative) operations on an underlying {!Mutable} data
  type, or a set of (functional) operations on an underlying {!Immutable} data
  type. A set of {!Immutable} operations is converted into a set of {!Mutable}
  ones, which can be used with a solver, by {!Immutable.from_immutable} which
  introduces a reference in the underlying data type and modifies the set of
  operations to update it in-place.

  @version VERSION()
  @author Timothy Bourke (INRIA)
  @author Marc Pouzet (LIENS)
  @cvode <node7#s:nvector> The NVECTOR Module
 *)

(**
  The type representing an nvector with underlying data of type ['a].

  @cvode <node7#s:nvector> N_Vector
 *)
type 'a nvector

(** Generic nvectors defined through sets of imperative operations on
    mutable data types.  *)
module Mutable :
  sig
    (**
       The set of operations required to define an {!nvector}. Some operations
       are optional; default values are either provided by the Ocaml interface
       or the Sundials library.

       @cvode <node7#s:nvector> _generic_N_Vector_Ops
     *)
    type 'a nvector_ops = {

      nvclone           : 'a -> 'a;
      (** Creates a new nvector of the same type as an existing vector.
          It need not copy the existing vector, but rather just allocate
          storage for the new vector. *)

      nvdestroy         : ('a -> unit) option;
      (** Destroys the N_Vector v and frees memory allocated for its internal
          data. *)

      nvspace           : ('a -> int * int) option;
      (** Returns storage requirements for one nvector. In the pair [(lrw,
          liw)], [lrw] is the number of realtype words required, and [liw] is
          the number of integer words required. *)

      nvlinearsum       : float -> 'a -> float -> 'a -> 'a -> unit;
      (** [nvlinearsum a x b y z] performs the operation
          [z] = [a]*[x] + [b]*[y], where [a] and [b] are scalars and
          [x] and [y] are vectors:
          [z]({i i}) = [a]*[x]({i i}) + [b]*[y]({i i}). *)

      nvconst           : float -> 'a -> unit;
      (** [nvconst c z] sets all components of [z] to [c]: [z]({i i}) = c. *)

      nvprod            : 'a -> 'a -> 'a -> unit;
      (** [nvprod x y z] sets [z] to be the component-wise product of [x]
          and [y]: [z]({i i}) = x({i i}) * y({i i}). *)

      nvdiv             : 'a -> 'a -> 'a -> unit;
      (** [nvdiv x y z] sets [z] to be the component-wise ratio of [x] and
          [y]: [z]({i i}) = [x]({i i}) / [y]({i i}).
          This function should only be called with a [y] whose components
          are all guaranteed to be nonzero. *)

      nvscale           : float -> 'a -> 'a -> unit;
      (** [nvscale c x z] scales [x] by [c] and returns the result in [z]:
          [z]({i i}) = [c] * [x]({i i}). *)

      nvabs             : 'a -> 'a -> unit;
      (** [nvabs x z] sets the components of [z] to the absolute values of
          the components of [x]: [z]({i i}) = |[x]({i i})|. *)

      nvinv             : 'a -> 'a -> unit;
      (** [nvinv x z] sets the components of [z] to be the inverses of the
         components of [x]: [z]({i i}) = 1.0 / [x]({i i}).
         This function should only be called with an [x] whose
         components are all guaranteed to be nonzero. *)

      nvaddconst        : 'a -> float -> 'a -> unit;
      (** [nvaddconst x b z] adds [b] to all components of [x] and
          returns the result in [z]: [z]({i i}) = [x]({i i}) + [b]. *)

      nvmaxnorm         : 'a -> float;
      (** [m = nvmaxnorm x] returns the maximum norm of [x]:
          [m] = |[x]({i i})|. *)

      nvwrmsnorm        : 'a -> 'a -> float;
      (** [m = nvwrmsnorm x w] returns the weighted root-mean-square norm of
          [x] with weight vector [w]:
            [m] = sqroot( sum( sqr([x]({i i}) * w({i i})) ) / n ). *)

      nvmin             : 'a -> float;
      (** [m = nvmin(x)] returns the smallest element of [x],
          [m] = min([x]({i i})). *)

      nvdotprod         : ('a -> 'a -> float) option;
      (** [d = nvdotprod x y] returns the ordinary dot product of [x] and [y],
          [d] = sum([x]({i i}) * [y]({i i})). *)

      nvcompare         : (float -> 'a -> 'a -> unit) option;
      (** [nvcompare c x z] compares the components of [x] to the scalar [c]
          and returns [z] such that [z]({i i}) = 1.0 if |[x]({i i})| >= [c]
          and [z]({i i}) = 0.0 otherwise. *)

      nvinvtest         : ('a -> 'a -> bool) option;
      (** [t = nvinvtest x z] sets the components of [z] to be the inverses of
          the components of [x], with prior testing for zero values:
            [z]({i i}) = 1.0 / [x]({i i}).
          This routine returns [true] if all components of [x] are nonzero
          (successful inversion) and [false] otherwise. *)

      nvwl2norm         : ('a -> 'a -> float) option;
      (** [m = nvwl2norm x w] returns the weighted Euclidean l_2 norm of [x]
          with weight vector [w]
          [m] = sqroot( sum( sqr([x]({i i}) * w({i i})) ) ). *)

      nvl1norm          : ('a -> float) option;
      (** [m = nvl1norm x] returns the l_1 norm of [x]:
          [m] = sum(|x({i i})|) *)

      nvwrmsnormmask    : ('a -> 'a -> 'a -> float) option;
      (** [m = nvwrmsnormmask x w id] returns the weighted root mean square
          norm of [x] with weight vector [w] built using only the elements
          of [x] corresponding to nonzero elements of [id]:
            [m] = sqroot( sum( sqr([x]({i i}) * w({i i})
            * sign(id({i i}))) ) / n ).
       *)

      nvconstrmask      : ('a -> 'a -> 'a -> bool) option;
      (** [t = nvconstrmask c x m] performs the following constraint tests:
            - [x]({i i}) > 0 if [c]({i i})  = 2,
            - [x]({i i}) >= 0 if [c]({i i}) = 1,
            - [x]({i i}) <= 0 if [c]({i i}) = -1,
            - [x]({i i}) < 0 if [c]({i i})  = -2.

          There is no constraint on [x]({i i}) if [c]({i i}) = 0.
          This routine returns [false] if any element failed the constraint
          test, and [true] if all passed. It also sets a mask vector [m],
          with elements equal to 1.0 where the constraint test failed,
          and 0.0 where the test passed. This routine is used only for
          constraint checking. *)

      nvminquotient     : ('a -> 'a -> float) option;
      (** [minq = nvminquotient num denom] returns the minimum of the
          quotients obtained by term-wise dividing [num]({i i}) by
          [denom]({i i}). A zero element in [denom] will be skipped.
          If no such quotients are found, then {!Sundials.big_real}
          is returned. *)
    }

    (** [make_nvector ops] takes a set of operations on the data
        type ['a] and yields a function for lifting values of type ['a]
        into ['a] {!nvector}s which can be passed to a solver (like
        {!Cvode_nvector}). *)
    val make_nvector    : 'a nvector_ops -> 'a -> 'a nvector

    (** Extracts the data from an {!nvector}. *)
    val nvector_data    : 'a nvector -> 'a

    (** [add_tracing p ops] modifies a set of {!nvector_ops} so that
        a message, prefixed by [p], is printed each time an operation
        is called. This function is intended to help debug sets of
        vector operations. *)
    val add_tracing     : string -> 'a nvector_ops -> 'a nvector_ops
  end

(** Generic nvectors defined through sets of functional operations on
    immutable data types.  *)
module Immutable :
  sig
    type 'a nvector_ops = {
      nvclone           : 'a -> 'a;
      (** Creates a new nvector of the same type as an existing vector.
          It need not copy the existing vector, but rather just allocate
          storage for the new vector. *)

      nvdestroy         : ('a -> unit) option;
      (** Destroys the N_Vector v and frees memory allocated for its internal
          data. *)

      nvspace           : ('a -> int * int) option;
      (** Returns storage requirements for one nvector. In the pair [(lrw,
          liw)], [lrw] is the number of realtype words required, and [liw] is
          the number of integer words required. *)

      nvlinearsum       : float -> 'a -> float -> 'a -> 'a;
      (** [z = nvlinearsum a x b y] performs the operation
          [z] = [a]*[x] + [b]*[y], where [a] and [b] are scalars and
          [x] and [y] are vectors:
          [z]({i i}) = [a]*[x]({i i}) + [b]*[y]({i i}). *)

      nvconst           : float -> 'a;
      (** [z = nvconst c] returns a [z] with all components equal to [c]:
          [z]({i i}) = c. *)

      nvprod            : 'a -> 'a -> 'a;
      (** [z = nvprod x y] returns the component-wise product of [x]
          and [y]: [z]({i i}) = x({i i}) * y({i i}). *)

      nvdiv             : 'a -> 'a -> 'a;
      (** [z = nvdiv x y] returns the component-wise ratio of [x] and
          [y]: [z]({i i}) = [x]({i i}) / [y]({i i}).
          This function should only be called with a [y] whose components
          are all guaranteed to be nonzero. *)

      nvscale           : float -> 'a -> 'a;
      (** [z = nvscale c x] returns the result of scaling [x] by [c]:
          [z]({i i}) = [c] * [x]({i i}). *)

      nvabs             : 'a -> 'a;
      (** [z = nvabs x] returns the absolute values of the components of [x]:
          [z]({i i}) = |[x]({i i})|. *)

      nvinv             : 'a -> 'a;
      (** [z = nvinv x] returns the inverses of the components of [x]:
          [z]({i i}) = 1.0 / [x]({i i}).
          This function should only be called with an [x] whose
          components are all guaranteed to be nonzero. *)

      nvaddconst        : 'a -> float -> 'a;
      (** [z = nvaddconst x b] returns the result of adding [b] to all
          components of [x]: [z]({i i}) = [x]({i i}) + [b]. *)

      nvmaxnorm         : 'a -> float;
      (** [m = nvmaxnorm x] returns the maximum norm of [x]:
          [m] = |[x]({i i})|. *)

      nvwrmsnorm        : 'a -> 'a -> float;
      (** [m = nvwrmsnorm x w] returns the weighted root-mean-square norm of
          [x] with weight vector [w]:
            [m] = sqroot( sum( sqr([x]({i i}) * w({i i})) ) / n ). *)

      nvmin             : 'a -> float;
      (** [m = nvmin(x)] returns the smallest element of [x],
          [m] = min([x]({i i})). *)

      nvdotprod         : ('a -> 'a -> float) option;
      (** [d = nvdotprod x y] returns the ordinary dot product of [x] and [y],
          [d] = sum([x]({i i}) * [y]({i i})). *)

      nvcompare         : (float -> 'a -> 'a) option;
      (** [z = nvcompare c x] compares the components of [x] to the scalar [c]
          and returns [z] such that [z]({i i}) = 1.0 if |[x]({i i})| >= [c]
          and [z]({i i}) = 0.0 otherwise. *)

      nvinvtest         : ('a -> 'a -> bool) option;
      (** [t = nvinvtest x z] sets the components of [z] to be the inverses of
          the components of [x], with prior testing for zero values:
            [z]({i i}) = 1.0 / [x]({i i}).
          This routine returns [true] if all components of [x] are nonzero
          (successful inversion) and [false] otherwise. *)

      nvwl2norm         : ('a -> 'a -> float) option;
      (** [m = nvwl2norm x w] returns the weighted Euclidean l_2 norm of [x]
          with weight vector [w]
          [m] = sqroot( sum( sqr([x]({i i}) * w({i i})) ) ). *)

      nvl1norm          : ('a -> float) option;
      (** [m = nvl1norm x] returns the l_1 norm of [x]:
          [m] = sum(|x({i i})|) *)

      nvwrmsnormmask    : ('a -> 'a -> 'a -> float) option;
      (** [m = nvwrmsnormmask x w id] returns the weighted root mean square
          norm of [x] with weight vector [w] built using only the elements
          of [x] corresponding to nonzero elements of [id]:
            [m] = sqroot( sum( sqr([x]({i i}) * w({i i})
            * sign(id({i i}))) ) / n ).
       *)

      nvconstrmask      : ('a -> 'a -> 'a -> bool) option;
      (** [t = nvconstrmask c x m] performs the following constraint tests:
            - [x]({i i}) > 0 if [c]({i i})  = 2,
            - [x]({i i}) >= 0 if [c]({i i}) = 1,
            - [x]({i i}) <= 0 if [c]({i i}) = -1,
            - [x]({i i}) < 0 if [c]({i i})  = -2.

          There is no constraint on [x]({i i}) if [c]({i i}) = 0.
          This routine returns [false] if any element failed the constraint
          test, and [true] if all passed. It also sets a mask vector [m],
          with elements equal to 1.0 where the constraint test failed,
          and 0.0 where the test passed. This routine is used only for
          constraint checking. *)

      nvminquotient     : ('a -> 'a -> float) option;
      (** [minq = nvminquotient num denom] returns the minimum of the
          quotients obtained by term-wise dividing [num]({i i}) by
          [denom]({i i}). A zero element in [denom] will be skipped.
          If no such quotients are found, then {!Sundials.big_real}
          is returned. *)
    }

    (** Transforms a set of vector operations on an immutable data type into a
        set of vector operations on references to that data type. *)
    val from_immutable  : 'a nvector_ops -> 'a ref Mutable.nvector_ops

    (** [make_nvector ops] takes a set of operations on the data
        type 'a and yields a function for lifting values of type ['a ref]
        into ['a ref] {!nvector}s which can be passed to a solver (like
        {!Cvode_nvector}). *)
    val make_nvector    : 'a nvector_ops -> 'a ref -> 'a ref nvector

    (** Extracts the data from an {!nvector}. *)
    val nvector_data    : 'a ref nvector -> 'a
  end

