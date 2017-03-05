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
type continuous = { mutable pos: float; mutable der: float }

type zerocrossing = { mutable zin: bool; mutable zout: float }

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
        (* allocate the initial state *)
	maxsize : 's -> int * int;
	(* returns the max length of the *)
	(* cvector and zvector *)
	cin : 's -> cvec -> int ->int;
	(* [cin cvec i = j] copies cvec into the internal state from *)
	(* position [i]. Return the current position [j] *)
	cout : 's -> cvec -> int -> int;
	(* [cout cvec i = j] copies the internal state into cvec *)
	dout : 's -> dvec -> int -> int;
	(* output the internal derivative *)
	zin : 's -> zinvec -> int -> int;
	(* copies zinvec into the internal state unit *)
	clear_zin : 's -> unit;
	(* sets the internal zero-crossings to false *)
	dzero : 's -> unit;
	(* sets the internal derivatives to 0.0 *)
	zout : 's -> zoutvec -> int -> int;
	(* copies the internal state into zoutvec *)
	step : 's -> 'a -> 'b;
	(* computes a step *)
	reset : 's -> unit;
	(* resets the state *)
	horizon : 's -> time;
	(* gives the next time horizon *)
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
				
