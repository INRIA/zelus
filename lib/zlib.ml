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
type zinvec = float array
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
					
(*
csize : 's -> int;
	(* the current size of the continuous state [cvec] *)
	zsize : 's -> int;
	 (* the current size of the zero-crossing vector [zinvec] *)
 *)
