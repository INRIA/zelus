(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

open Ztypes

(* From zls.ml *)
open Bigarray
type carray = (float, float64_elt, c_layout) Array1.t
type zarray = (int32, int32_elt,   c_layout) Array1.t

(*
  open Ztypes

  let der = machine(derivative) {
    memories
      gindex : int = 0
    instances
      method alloc = { ... }
      method der (x': float) = ()
      method set (x : float) = ()
      method get = 0.
  }

  let ders = machine(derivatives) {
    memories
      gindex : int = 0
    instances
      method alloc (n: int) = { ... }
      method der ((i: int), (x': float)) = ()
      method set ((i: int), (x : float)) = ()
      method get (i: int) = 0.
  }

  let crossing = machine(zerocrossing) {
    memories
      gindex : int = 0
    instances
      method alloc = { ... }
      method set (e: float) = ()
      method get = true
  }

  let crossings = machine(zerocrossings) {
    memories
      gindex : int = 0
    instances
      method alloc (n: int) = { ... }
      method set ((i: int), (e: float)) = ()
      method get = true
  }
*)

(* Interface *)

type derivative =
  Der: {
    alloc : unit -> 's;
    der   : 's -> float -> unit;
    set   : 's -> float -> unit;
    get   : 's -> float;
  } -> derivative

type derivatives =
  Ders: {
    alloc : int -> 's;
    der   : 's -> (int * float) -> unit;
    set   : 's -> (int * float) -> unit;
    get   : 's -> int -> float;
  } -> derivatives

type crossing =
  Zero: {
    alloc : unit -> 's;
    set   : 's -> float -> unit;
    get   : 's -> bool;
  } -> crossing

type crossings =
  Zeros: {
    alloc : int -> 's;
    set   : 's -> (int * float) -> unit;
    get   : 's -> int -> bool;
  } -> crossings

(* Implementations *)

let cin  = ref (Array1.create Float64 C_layout 0)
let dout = ref (Array1.create Float64 C_layout 0)
let zin  = ref (Array1.create Int32 C_layout 0)
let zout = ref (Array1.create Float64 C_layout 0)

let max_der = ref 0
let max_zero = ref 0

(* derivative *)

let der_alloc () =
  let r = !max_der in
  incr max_der; r

let der = Der {
    alloc = der_alloc;
    der = Array1.set !dout;
    set = Array1.set !cin;
    get = Array1.get !cin;
  }

(* derivatives *)

let ders_alloc n =
  let r = !max_der in
  max_der := !max_der + n; r

let ders_der s (i, v) = Array1.set !dout (s + i) v
let ders_set s (i, v) = Array1.set !cin (s + i) v
let ders_get s i = Array1.get !cin (s + i)

let ders = Ders {
    alloc = ders_alloc;
    der   = ders_der;
    set   = ders_set;
    get   = ders_get;
  }

(* crossing *)

let crossing_alloc () =
  let r = !max_zero in
  incr max_zero; r

let crossing_get s = Array1.get !zin s <> 0l

let crossing = Zero {
    alloc = crossing_alloc;
    set = Array1.set !zout;
    get = crossing_get;
  }

(* crossings *)

let crossings_alloc n =
  let r = !max_zero in
  max_zero := !max_zero + n; r

let crossings_set s (i, v) = Array1.set !zout (s + i) v
let crossings_get s i = Array1.get !zin (s + i) <> 0l

let crossing = Zeros {
    alloc = crossings_alloc;
    set = crossings_set;
    get = crossings_get;
  }

