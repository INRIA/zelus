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

(** {!Nvector.nvector}s for standard arrays and one-dimensional bigarrays

  @version VERSION()
  @author Timothy Bourke (INRIA)
  @author Marc Pouzet (LIENS)
  @see <OCAML_DOC_ROOT(Array)> Array
  @see <OCAML_DOC_ROOT(Bigarray.Array1)> Bigarray.Array1
 *)

(** An abstract set of functions for working manipulating {!Nvector.nvector}s
    where the underlying data structure is an array of [float]s.  *)
module type ARRAY_NVECTOR =
  sig
    (** The type of array used within the {!Nvector.nvector}. *)
    type t

    (** The set of nvector operations on an array.
        
        These operations can be called directly if necessary, for example:
{[let vmax_norm = Nvector_array.Bigarray.array_nvec_ops.Nvector.Mutable.nvmaxnorm in
let vn = vmax_norm u]}
     
     *)
    val array_nvec_ops  : t Nvector.Mutable.nvector_ops

    (** [make n x] creates an {!Nvector.nvector} containing an array
        of [n] elements, each of which is equal to [x]. *)
    val make            : int -> float -> t Nvector.nvector

    (** Lifts an array to an nvector. *)
    val wrap            : t -> t Nvector.nvector

    (** Extracts an array from an nvector. *)
    val data            : t Nvector.nvector -> t
  end

(** {!Nvector.nvector} on {{:OCAML_DOC_ROOT(Array)} Array}s of [float]s. *)
include ARRAY_NVECTOR with type t = float array
 
(** {!Nvector.nvector} on {{:OCAML_DOC_ROOT(Bigarray.Array1)} Bigarray}s
   of [float]s. *)
module Bigarray :
  ARRAY_NVECTOR
  with
    type t = (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array1.t

