(**************************************************************************)
(*                                                                        *)
(*                                Zelus                                   *)
(*               A synchronous language for hybrid systems                *)
(*                       http://zelus.di.ens.fr                           *)
(*                                                                        *)
(*                    Marc Pouzet and Timothy Bourke                      *)
(*                                                                        *)
(*  Copyright 2012 - 2019. All rights reserved.                           *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(*  Zelus is developed in the INRIA PARKAS team.                          *)
(*                                                                        *)
(**************************************************************************)

(* Type declarations and values that must be linked with *)
(* the generated code *)
type 'a continuous = { mutable pos: 'a; mutable der: 'a }

type ('a, 'b) zerocrossing = { mutable zin: 'a; mutable zout: 'b }

type 'a signal = 'a * bool
type zero = bool

(*
type ('a, 'b) hybrid =
    Hybrid:
      { alloc : unit -> 's; (* allocate the state *)
        step : 's -> 'a -> 'b; (* compute a step *)
        reset : 's -> unit; (* reset/inialize the state *)
      } -> ('a, 'b) hybrid
 *)
	      
type ('a, 'b) node =
    Node:
      { alloc : unit -> 's; (* allocate the state *)
        step : 's -> 'a -> 'b; (* compute a step *)
        reset : 's -> unit; (* reset/inialize the state *)
      } -> ('a, 'b) node

open Bigarray

type time = float
type cvec = (float, float64_elt, c_layout) Array1.t
type dvec = (float, float64_elt, c_layout) Array1.t
type zinvec = (int32, int32_elt,   c_layout) Array1.t
type zoutvec = (float, float64_elt, c_layout) Array1.t

(* The interface with the solver *)
type cstate =
  { mutable dvec : dvec; (* the vector of derivatives *)
    mutable cvec : cvec; (* the vector of positions *)
    mutable zinvec : zinvec; (* the vector of boolean; true when the
                             solver has detected a zero-crossing *)
    mutable zoutvec : zoutvec; (* the corresponding vector that define
                               zero-crossings *)
    mutable cstart : int; (* the start position in the vector of positions *)
    mutable zstart : int; (* the start position in the vector of zero-crossings *)
    mutable cend : int; (* the maximum size of the vector of positions *)
    mutable zend : int; (* the maximum number of zero-crossings *)
    mutable horizon : float; (* the next horizon *)
    mutable discrete : bool; (* integration iff [discrete = false] *)
  }

type ('a, 'b) hnode =
    Hnode:
      { alloc : unit -> 's; (* allocate the state *)
        csize : 's -> int; (* the number of current state variables *)
        zsize : 's -> int; (* the number of current zero crossings *)
        cmaxsize: 's -> int; (* the max number of state variables *)
        zmaxsize: 's -> int; (* the max number of zero crossings *)
        step : 's -> 'a -> 'b; (* compute a step *)
        reset : 's -> unit; (* reset/inialize the state *)
        derivative: 's -> cvec -> dvec -> unit; (* computes the derivative *)
        crossings: 's -> cvec -> zinvec -> zoutvec -> unit; (* zero crossings *)
        horizon: 's -> time; (* the next time horizon *)
      } -> ('a, 'b) hnode

type 'o hsimu =
    Hsim:
      { alloc : unit -> 's;
        (* allocate the initial state *)
        maxsize : 's -> int * int;
        (* returns the max length of the *)
        (* cvector and zvector *)
        csize : 's -> int;
        (* returns the current length of the continuous state vector *)
        zsize : 's -> int;
        (* returns the current length of the zero-crossing vector *)
        step : 's -> cvec -> dvec -> zinvec -> time -> 'o;
        (* computes a step *)
        derivative : 's -> cvec -> dvec -> zinvec -> zoutvec -> time -> unit;
        (* computes the derivative *)
        crossings : 's -> cvec -> zinvec -> zoutvec -> time -> unit;
        (* computes the derivative *)
        reset : 's -> unit;
        (* resets the state *)
        horizon : 's -> time;
        (* gives the next time horizon *)
      } -> 'o hsimu

(* The interface with the solver *)
(* Warning: this interface is not used for the moment *)
(* type cstate =
  { mutable dvec : dvec; (* the vector of derivatives *)
    mutable cvec : cvec; (* the vector of positions *)
    mutable zin : zinvec; (* the vector of boolean; true when the
                             solver has detected a zero-crossing *)
    mutable zout : zoutvec; (* the corresponding vector that define
                               zero-crossings *)
    mutable cpos : int; (* the start position in the vector of positions *)
    mutable zpos : int; (* the start position in the vector of zero-crossings *)
    mutable cmax : int; (* the maximum size of the vector of positions *)
    mutable zmax : int; (* the maximum number of zero-crossings *)
    mutable horizon : float; (* the next horizon *)
    mutable discrete : bool; (* integration when true *)
  }  *)
