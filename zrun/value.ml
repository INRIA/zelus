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

type 'a extended =
  | Vnil : 'a extended
  | Vbot : 'a extended
  | Value : 'a -> 'a extended
  
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
  | Vtuple : value list -> pvalue
  | Vstuple : pvalue list -> pvalue
  | Vstate0 : Ident.t -> pvalue
  | Vstate1 : Ident.t * pvalue list -> pvalue
  | Vfun : (pvalue -> pvalue option) -> pvalue
  | Vnode : (state, value, value) instance -> pvalue
  | Vclosure : Zelus.funexp * pvalue Genv.genv * value Ident.Env.t -> pvalue
                                   
and value = pvalue extended
          
and state =
  | Sempty : state
  | Stuple : state list -> state
  | Sval : value -> state
  | Sopt : value option -> state
  | Sinstance : (state, value, value) instance -> state
  | Scstate : { pos : value; der : value } -> state 
  | Szstate : { zin : value; zout : value } -> state
  
and ('s, 'a, 'b) instance =
  { init : 's;
    step : 's -> 'a -> ('b * 's) option
  }
  
(* an input entry in the environment *)
type 'a ientry = { cur: 'a; last : 'a option; default : 'a option }

and 'a default =
  | Val : 'a default
  | Last : 'a -> 'a default
  | Default : 'a -> 'a default

type ('a, 's) costream =
  | CoF : { init : 's;
            step : 's -> ('a * 's) option } ->
          ('a, 's) costream

type ('a, 'b, 's) node =
  | CoFun : ('a list -> 'b option) -> ('a, 'b, 's) node
  | CoNode : { init : 's;
               step : 's -> 'a list -> ('b * 's) option } -> ('a, 'b, 's) node
 
