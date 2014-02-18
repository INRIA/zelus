(***********************************************************************)
(*                                                                     *)
(*              Ocaml interface to Sundials CVODE solver               *)
(*                                                                     *)
(*       Timothy Bourke (INRIA Rennes) and Marc Pouzet (LIENS)         *)
(*                                                                     *)
(*  Copyright 2011 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Library General Public License, with    *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

module type ARRAY_NVECTOR =
  sig
    type t

    val array_nvec_ops  : t Nvector.Mutable.nvector_ops
    val make            : int -> float -> t Nvector.nvector
    val wrap            : t -> t Nvector.nvector
    val data            : t Nvector.nvector -> t
  end

module NvectorFn =
  functor (A : sig
      type data
      val get       : data -> int -> float
      val set       : data -> int -> float -> unit
      val fill      : data -> float -> unit
      val make      : int -> float -> data
      val copy      : data -> data
      val length    : data -> int
      val fold_left : ('a -> float -> 'a) -> 'a -> data -> 'a
    end) ->
  struct
    type t = A.data

    let lift_bop f x y z =
      for i = 0 to A.length x - 1 do
        A.set z i (f (A.get x i) (A.get y i))
      done

    let lift_op f x z =
      for i = 0 to A.length x - 1 do
        A.set z i (f (A.get x i))
      done

    let zip_fold_left f iv x y =
      let a = ref iv in
      for i = 0 to A.length x - 1 do
        a := f !a (A.get x i) (A.get y i)
      done;
      !a

    let triple_zip_fold_left f iv x y z =
      let a = ref iv in
      for i = 0 to A.length x - 1 do
        a := f !a (A.get x i) (A.get y i) (A.get z i)
      done;
      !a

    let arr_nvlinearsum a x b y =
      lift_bop (fun x y -> a *. x +. b *. y) x y

    let arr_nvconst c a = A.fill a c

    let arr_nvaddconst x b = lift_op (fun x -> x +. b) x

    let arr_nvmaxnorm =
      let f max x =
        let ax = abs_float x in
        if ax > max then ax else max
      in A.fold_left f 0.0

    let arr_nvwrmsnorm x w =
      let f a x w = a +. ((x *. w) ** 2.0) in
      sqrt ((zip_fold_left f 0.0 x w) /. float (A.length x))

    let arr_nvwrmsnormmask x w id =
      let f a id x w =
        if id > 0.0 then a +. ((x *. w) ** 2.0) else a
      in
      sqrt ((triple_zip_fold_left f 0.0 id x w) /. float (A.length x))

    let arr_nvmin =
      let f min x = if x < min then x else min
      in A.fold_left f max_float

    let arr_nvdotprod =
      let f a x y = a +. x *. y in
      zip_fold_left f 0.0

    let arr_nvcompare c =
      lift_op (fun x -> if abs_float x >= c then 1.0 else 0.0)

    let arr_nvinvtest x z =
      let l = A.length x in
      let rec f i =
        if i = l then true
        else if (A.get x i) = 0.0 then false
        else (A.set z i (1.0 /. (A.get x i)); f (i + 1))
      in f 0

    let arr_nvwl2norm x w =
      let f a x w = a +. ((x *. w) ** 2.0) in
      sqrt (zip_fold_left f 0.0 x w)

    let arr_nvl1norm =
      let f a x = a +. abs_float x in
      A.fold_left f 0.0

    let arr_nvconstrmask c x m =
      let test = ref true in
      let check b = if b then 0.0 else (test := false; 1.0) in
      let f c x =
        match c with
        |  2.0 -> check (x >  0.0)
        |  1.0 -> check (x >= 0.0)
        | -1.0 -> check (x <= 0.0)
        | -2.0 -> check (x <  0.0)
        |  0.0 -> 0.0
        |    _ -> assert false
      in
      lift_bop f c x m;
      !test

    let arr_nvminquotient =
      let f m n d =
        if d = 0.0 then m
        else min m (n /. d)
      in
      zip_fold_left f Sundials.big_real

    let array_nvec_ops = {
          Nvector.Mutable.nvclone        = A.copy;
          Nvector.Mutable.nvdestroy      = None;
          Nvector.Mutable.nvspace        = None;
          Nvector.Mutable.nvlinearsum    = arr_nvlinearsum;
          Nvector.Mutable.nvconst        = arr_nvconst;
          Nvector.Mutable.nvprod         = lift_bop ( *. );
          Nvector.Mutable.nvdiv          = lift_bop ( /. );
          Nvector.Mutable.nvscale        = (fun c -> lift_op (fun x -> c *. x));
          Nvector.Mutable.nvabs          = lift_op abs_float;
          Nvector.Mutable.nvinv          = lift_op (fun x -> 1.0 /. x);
          Nvector.Mutable.nvaddconst     = arr_nvaddconst;
          Nvector.Mutable.nvmaxnorm      = arr_nvmaxnorm;
          Nvector.Mutable.nvwrmsnorm     = arr_nvwrmsnorm;
          Nvector.Mutable.nvmin          = arr_nvmin;
          Nvector.Mutable.nvdotprod      = Some arr_nvdotprod;
          Nvector.Mutable.nvcompare      = Some arr_nvcompare;
          Nvector.Mutable.nvinvtest      = Some arr_nvinvtest;
          Nvector.Mutable.nvwl2norm      = Some arr_nvwl2norm;
          Nvector.Mutable.nvl1norm       = Some arr_nvl1norm;
          Nvector.Mutable.nvwrmsnormmask = Some arr_nvwrmsnormmask;
          Nvector.Mutable.nvconstrmask   = Some arr_nvconstrmask;
          Nvector.Mutable.nvminquotient  = Some arr_nvminquotient;
    }

    let make n e =
      Nvector.Mutable.make_nvector array_nvec_ops (A.make n e)

    let wrap a =
      Nvector.Mutable.make_nvector array_nvec_ops a
      (* (Nvector.Mutable.add_tracing "::" array_nvec_ops) *)

    let data = Nvector.Mutable.nvector_data
  end

module Array = NvectorFn (
  struct
    type data = float array
    include Array
    let fill a c = fill a 0 (length a) c
  end)

module Bigarray = NvectorFn (
  struct
    include Bigarray.Array1

    type data = (float, Bigarray.float64_elt, Bigarray.c_layout) t

    let make n d =
      let arr = create Bigarray.float64 Bigarray.c_layout n in
      fill arr d;
      arr

    let length = dim

    let copy src =
      let dst = create Bigarray.float64 Bigarray.c_layout (length src) in
      blit src dst;
      dst

    let fold_left f a vs =
      let len = length vs - 1 in
      let a = ref a in
      for i = 0 to len do
        a := f !a vs.{i}
      done; !a
  end)

include Array

