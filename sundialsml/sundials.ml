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

let extra_precision = ref false

let print_time (s1, s2) t =
  if !extra_precision
  then Printf.printf "%s%.15e%s" s1 t s2
  else Printf.printf "%s%e%s" s1 t s2

external format_float : string -> float -> string
    = "caml_format_float"

let floata = format_float "%a"

external get_big_real : unit -> float
    = "cvode_ml_big_real"

let big_real = get_big_real ()

external get_unit_roundoff : unit -> float
    = "cvode_ml_unit_roundoff"

let unit_roundoff = get_unit_roundoff ()

type real_array =
  (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array1.t

let make_real_array =
  Bigarray.Array1.create Bigarray.float64 Bigarray.c_layout

type real_array2 =
  (float, Bigarray.float64_elt, Bigarray.c_layout) Bigarray.Array2.t

let make_real_array2 =
  Bigarray.Array2.create Bigarray.float64 Bigarray.c_layout

module Carray =
  struct
    type t = real_array

    let kind = Bigarray.float64
    let layout = Bigarray.c_layout
    let empty = Bigarray.Array1.create kind layout 0

    let create = Bigarray.Array1.create kind layout
    let of_array = Bigarray.Array1.of_array kind layout

    let fill = Bigarray.Array1.fill

    let length = Bigarray.Array1.dim

    let blit = Bigarray.Array1.blit

    let of_carray src =
      let dst = create (length src) in
      blit src dst;
      dst

    let app f v =
      for i = 0 to (length v - 1) do
        f v.{i}
      done

    let map f v =
      for i = 0 to (length v - 1) do
        v.{i} <- f v.{i}
      done

    let appi f v =
      for i = 0 to (length v - 1) do
        f i v.{i}
      done

    let mapi f v =
      for i = 0 to (length v - 1) do
        v.{i} <- f i v.{i}
      done

    let print_with_time t v =
      print_time ("", "") t;
      if !extra_precision
      then app (Printf.printf "\t% .15e") v
      else app (Printf.printf "\t% e") v;
      print_newline ()
  end

(* root arrays *)

type int_array = (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t
let make_int_array = Bigarray.Array1.create Bigarray.int32 Carray.layout

module Roots =
  struct
    type t = int_array
    type val_array = Carray.t

    type root_event =
      | NoRoot
      | Rising
      | Falling

    let reset v = Bigarray.Array1.fill v 0l

    let create n =
      let a = make_int_array n in
      reset a;
      a

    let empty = create 0

    let length = Bigarray.Array1.dim

    let get roots i = roots.{i} <> 0l

    let rising  roots i = roots.{i} = 1l
    let falling roots i = roots.{i} = -1l

    let from_int32 x =
      if x = 1l then Rising else if x = -1l then Falling else NoRoot

    let from_int x =
      if x = 1 then Rising else if x = -1 then Falling else NoRoot

    let to_int32 x =
      match x with
      | NoRoot -> 0l
      | Rising -> 1l
      | Falling -> -1l

    let to_int x =
      match x with
      | NoRoot -> 0
      | Rising -> 1
      | Falling -> -1

    let get' roots i = from_int32 roots.{i}

    let set a i v =
      Bigarray.Array1.set a i (to_int32 v)

    let set_rising a i v = set a i (if v then Rising else NoRoot)
    let set_falling a i v = set a i (if v then Falling else NoRoot)

    let appi f v =
      for i = 0 to (length v - 1) do
        f i (from_int32 v.{i})
      done

    let app f v =
      for i = 0 to (length v - 1) do
        f v.{i}
      done

    let print vs =
      app (Printf.printf "\t% ld") vs;
      print_newline ()

    let fold_left f a vs =
      let len = Bigarray.Array1.dim vs - 1 in
      let a = ref a in
      for i = 0 to len do
        a := f !a (Int32.to_int vs.{i})
      done;
      !a

    let exists = fold_left (fun a x -> a || x <> 0) false
  end

