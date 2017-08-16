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

(* Type declarations and values that must be linked with *)
(* the generated code *)
type 'a continuous = { mutable pos: 'a; mutable der: 'a }

type 'a zerocrossing = { mutable zin: 'a; mutable zout: 'a }

type 'a signal = 'a * bool
type zero = bool

type ('a, 'b) node =
    Node:
      { alloc : unit -> 's; (* allocate the state *)
        step : 's -> 'a -> 'b; (* compute a step *)
        reset : 's -> unit; (* reset/inialize the state *)
      } -> ('a, 'b) node

type time = float
type cvec = float array
type dvec = float array
type zinvec = int32 array
type zoutvec = float array
		    
type ('a, 'b) hybrid =
    Hybrid:
      { alloc : unit -> 's;
        step : 's -> 'a -> 'b;
	(* computes a step *)
	reset : 's -> unit;
	} -> ('a, 'b) hybrid
					
type hsimu =
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
        step : 's -> cvec -> zinvec -> unit;
	(* computes a step *)
	derivative : 's -> cvec -> dvec -> time -> unit;
	(* computes the derivative *)
	crossings : 's -> cvec -> zoutvec -> time -> unit;
	(* computes the derivative *)
	reset : 's -> unit;
	(* resets the state *)
	horizon : 's -> time;
	(* gives the next time horizon *)
	} -> hsimu
				
