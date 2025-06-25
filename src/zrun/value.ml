(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
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

type 'a result = ('a, Error.error) Result.t

type 'a star =
  | Vnil (* non initialized value *)
  | Vbot (* bottom value *)
  | Value of 'a (* value *)

type ('info, 'ienv) value = ('info, 'ienv) pvalue star

and ('info, 'ienv) pvalue =
  | Vint of int
  | Vbool of bool
  | Vfloat of float
  | Vchar of char
  | Vstring of string
  | Vvoid 
  | Vconstr0 of Lident.t
  | Vconstr1 of Lident.t * ('info, 'ienv) pvalue list
  | Vrecord of ('info, 'ienv) pvalue Zelus.record list
  | Vpresent of ('info, 'ienv) pvalue 
  | Vabsent 
  | Vstuple of ('info, 'ienv) pvalue list
  | Vtuple of ('info, 'ienv) pvalue star list
  | Vstate0 of Ident.t
  | Vstate1 of Ident.t * ('info, 'ienv) pvalue list
  | Varray of ('info, 'ienv) pvalue array
  (* imported stateless functions; they must verify that *)
  (* f(atomic v) not= bot *)
  | Vfun of (('info, 'ienv) pvalue -> ('info, 'ienv) pvalue option)
  | Vclosure of ('info, 'ienv) closure
  (* function parameterized by sizes *)
  | Vsizefun of ('info, 'ienv) sizefun
  (* a representation for mutually recursive functions over sizes *)
  (* f where rec [f1<s,...> = e1 and ... fk<s,...> = ek] *)
  | Vsizefix of 
      { bound: int list option; (* the maximum number of iterations *)
        name: Ident.t; (* name of the defined function *)
        defs: ('info, 'ienv) sizefun Ident.Env.t;
        (* the set of mutually recursive function definitions *) 
      }

and 'a array =
  | Vflat : 'a Array.t -> 'a array
  | Vmap : 'a map -> 'a array

(* bounded maps *)
(* [get x i = v if x.left <= i <= right then x i
                  else match otherwise with | None -> error 
                                            | Some(x) -> get x i *)
and 'a map =
  { m_length : int; m_u : int -> 'a result }
     
(* a size parameterized expression - f <n1,...,nk> = e *)
and ('info, 'ienv) sizefun = 
  { s_params: Ident.t list; 
    s_body: ('info, 'ienv) Zelus.exp; 
    s_genv: ('info, 'ienv) pvalue Genv.genv; 
    s_env: ('info, 'ienv) pvalue star ientry Ident.Env.t }
                                   
(* a functional value - [fun|node] x1 ... xn -> e *)
and ('info, 'ienv) closure =
  { c_funexp : ('info, 'ienv) Zelus.funexp;
    c_genv: ('info, 'ienv) pvalue Genv.genv;
    c_env: ('info, 'ienv) pvalue star ientry Ident.Env.t }
                                     
(* instance of a node *)
and ('info, 'ienv) instance =
  { init : ('info, 'ienv) state; (* current state *)
    step : ('info, 'ienv) closure; (* step function *)
  }

and ('info, 'ienv) state =
  | Sbot 
  | Snil 
  | Sempty 
  | Sval of ('info, 'ienv) value
  | Sstatic of ('info, 'ienv) pvalue
  | Slist of ('info, 'ienv) state list
  | Sopt of ('info, 'ienv) value option
  | Sinstance of ('info, 'ienv) instance
  | Scstate of { pos : ('info, 'ienv) value; der : ('info, 'ienv) value }
  | Szstate of { zin : bool; zout : ('info, 'ienv) value }
  | Shorizon of { zin : bool; horizon : float }
  | Speriod of
      { zin : bool; phase : float; period : float; horizon : float }
  (* environment of values *)
  | Senv of ('info, 'ienv) value ientry Ident.Env.t

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
