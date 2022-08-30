(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
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
type 'a ientry = { cur: 'a; last : 'a option; default : 'a option }

type 'a result = ('a, Error.error) Result.t

type 'a extended =
  | Vnil : 'a extended (* non initialized value *)
  | Vbot : 'a extended (* bottom value *)
  | Value : 'a -> 'a extended (* value *)
  
type pvalue =
  | Vint : int -> pvalue
  | Vbool : bool -> pvalue
  | Vfloat : float -> pvalue
  | Vchar : char -> pvalue
  | Vstring : string -> pvalue
  | Vvoid : pvalue
  | Vconstr0 : Lident.t -> pvalue
  | Vconstr1 : Lident.t * pvalue list -> pvalue
  | Vrecord : pvalue Zelus.record list -> pvalue
  | Vpresent : pvalue -> pvalue
  | Vabsent : pvalue
  | Vstuple : pvalue list -> pvalue
  | Vtuple : value list -> pvalue
  | Vstate0 : Ident.t -> pvalue
  | Vstate1 : Ident.t * pvalue list -> pvalue
  | Vfun : (pvalue -> pvalue option) -> pvalue (* inported stateless function *)
  | Vclosure : closure -> pvalue
  | Varray : pvalue Array.t -> pvalue

and closure =
  { c_funexp : Zelus.funexp;
    c_genv: pvalue Genv.genv;
    c_env: value ientry Ident.Env.t }
                                     
and value = pvalue extended

and state =
  | Sbot : state
  | Snil : state
  | Sempty : state
  | Sval : value -> state
  | Slist : state list -> state
  | Sopt : value option -> state
  | Sinstance : instance -> state
  | Scstate : { pos : value; der : value } -> state 
  | Szstate : { zin : bool; zout : value } -> state
  | Shorizon : { zin : bool; horizon : float } -> state
  | Speriod :
      { zin : bool; phase : float; period : float; horizon : float } -> state

(* instance of a node *)
and instance =
  { init : state; (* current state *)
    step : closure; (* step function *)
  }

(*
type ('a, 's) costream =
  | CoF : { init : 's;
            step : 's -> ('a * 's) option } ->
          ('a, 's) costream

type ('a, 'b, 's) node =
  | CoFun : ('a list -> 'b option) -> ('a, 'b, 's) node
  | CoNode : { init : 's;
               step : 's -> 'a list -> ('b * 's) option } -> ('a, 'b, 's) node
 *)
