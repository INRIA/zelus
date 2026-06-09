(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2026 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Set of values *)
(* noinitialized and non causal values *)

(* an input entry in the environment *)
type 'a ientry =
  { cur: 'a option; (* the current value of [x] *)
    last : 'a option; (* the value of [last x] *)
    default : 'a option; (* the default value of [x] *)
    reinit : bool; (* [last x] is defined by an equation [init x = ...] *)
  }

type 'a env = 'a ientry Ident.Env.t

type 'a result = ('a, Error.error) Result.t

type 'a star =
  | Vnil (* non initialized value *)
  | Vbot (* bottom value *)
  | Value of 'a (* value *)

type value = pvalue star

and pvalue =
  | Vint of int
  | Vbool of bool
  | Vfloat of float
  | Vchar of char
  | Vstring of string
  | Vvoid 
  | Vconstr0 of Lident.t
  | Vconstr1 of Lident.t * pvalue list
  | Vrecord of pvalue Zelus.record list
  | Vpresent of pvalue 
  | Vabsent 
  | Vstuple of pvalue list
  | Vtuple of pvalue star list
  | Vstate0 of Ident.t
  | Vstate1 of Ident.t * pvalue list
  | Varray of pvalue array
  (* imported stateless functions; they are strict, that is *)
  (* f(atomic v) not= bot *)
  | Vifun of (pvalue -> pvalue option)
  (* user defined functions and nodes *)
  | Vfun of vfun
  | Vnode of vnode
  (* functions parameterized by a tuple of sizes *)
  | Vsizefun of sizefun

and 'a array =
  | Vflat of 'a Array.t (* the array is explicit *)
  | Vmap of 'a map (* or implicit *)

(* bounded maps *)
(* [get x i = v if x.left <= i <= right then x i
                  else match otherwise with | None -> error 
                                            | Some(x) -> get x i *)
and 'a map =
  { m_length : int; m_u : int -> 'a result }

and sizefun =
  { s_arity: int; (* expected number of size arguments *)
    s_fun: int list -> value result;
    s_bound: int list option; (* the maximum number of iterations *)
  }

(* combinational function definitions are currified; *)
(* they are of the form [fun (x1,...) ... (xn,...) -> e] *)
and vfun =
  { f_arity: int;
    f_no_input: bool; (* [fun () -> e] *)
    f_fun : value list -> value result (* [f (e1,...) ... (en,...)] *)
  }

(* stateful (node or hybrid) functions are uncurryfied *)
(* [node|hybrid (x1,...,xn) -> e] *)
and vnode =
  { n_tkind: Zelus.tkind; (* either discrete-time or continuous-time *)
    n_arity: int;
    n_no_input: bool; (* [node|hybrid () -> e] *)
    n_init : state; (* current state *)
    (* step function *)
    n_step : state -> value -> (value * state) result; (* [f s v] *)
  }

and instance = vnode

(* the type for a state *)
and state =
  | Sbot 
  | Snil 
  | Sempty 
  | Sval of value
  | Sstatic of pvalue
  | Slist of state list
  | Sopt of value option
  | Sinstance of instance
  | Scstate of { pos : value; der : value }
  | Szstate of { zin : bool; zout : value }
  | Shorizon of { zin : bool; horizon : float }
  | Speriod of
      { zin : bool; phase : float; period : float; horizon : float }
  (* environment of values *)
  | Senv of value ientry Ident.Env.t

(*
  An expression is interpreted as a value of type:

  type ('a, 's) costream =
  | CoF : { init : 's;
            step : 's -> ('a * 's) option } ->
          ('a, 's) costream

  A functional value, combinatorial or stateful is interpreted as a value of type:

  type ('a, 'b, 's) node =
  | CoFun : ('a list -> 'b option) -> ('a, 'b, 's) node
  | CoNode : { init : 's;
               step : 's -> 'a -> ('b * 's) option } -> ('a, 'b, 's) node

  Here, the set of values ('a value) contains all the possible
  values; those that are produced at compile time or instanciation time; and
  those that are produced at every reaction time. The two could be separated,
  in particular dynamic values (e.g., functions) could be allowed only
  at compilation and instantiation time; not at execution time.
*)
