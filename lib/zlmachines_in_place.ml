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

(* The same as Zlmachines except that the array for storing the *)
(* derivative, position and zero-crossing are written in place *)
(* from left to right. The worst size is less than [max_der] and *)
(* [max_zero] but between two discrete steps, the valid values *)
(* are between [0] and [cur_der] and [cur_zero] *)
                                             
(*
  open Ztypes

  let der = machine(derivative) {
    instances
      method alloc = { ... }
      method der (x': float) = ()
      method set (x : float) = ()
      method get = 0.
  }

  let ders = machine(derivatives) {
    instances
      method alloc (n: int) = { ... }
      method der ((i: int), (x': float)) = ()
      method set ((i: int), (x : float)) = ()
      method get (i: int) = 0.
  }

  let crossing = machine(zerocrossing) {
    instances
      method alloc = { ... }
      method set (e: float) = ()
      method get = true
  }

  let crossings = machine(zerocrossings) {
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
let cur_der = ref 0
let cur_zero = ref 0
                   
(* derivative *)

let der_alloc () =
  incr max_der

let der s v = Array1.set !dout !cur_der v; incr cur_der
let set s x = Array1.set !cin !cur_der x; incr cur_der
let get s = Array1.get !cin !cur_der
                       
let der = Der {
    alloc = der_alloc;
    der = der;
    set = set;
    get = get;
  }

(* derivatives *)

let ders_alloc n =
  max_der := !max_der + n

let ders_der s (i, v) = Array1.set !dout (!cur_der + i) v; incr cur_der
let ders_set s (i, v) = Array1.set !cin (!cur_der + i) v; incr cur_der
let ders_get s i = Array1.get !cin (!cur_der + i)

let ders = Ders {
    alloc = ders_alloc;
    der   = ders_der;
    set   = ders_set;
    get   = ders_get;
  }

(* crossing *)

let crossing_alloc () =
  incr max_zero

let crossing_set s v = Array1.set !zout !cur_zero v; incr cur_zero

let crossing_get s = Array1.get !zin !cur_zero <> 0l

let crossing = Zero {
    alloc = crossing_alloc;
    set = crossing_set;
    get = crossing_get;
  }

(* crossings *)

let crossings_alloc n =
  max_zero := !max_zero + n

let crossings_set s (i, v) =
  Array1.set !zout (!cur_zero + i) v; incr cur_zero

let crossings_get s i =
  let r = Array1.get !zin (!cur_zero + i) <> 0l in
  incr cur_zero;
  r

let crossing = Zeros {
    alloc = crossings_alloc;
    set = crossings_set;
    get = crossings_get;
  }

