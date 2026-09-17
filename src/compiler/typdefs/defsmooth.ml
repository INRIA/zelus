(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2026 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* smoothness *)
(* base types 0, 1/2 and 1; order 0 < 1/2 < 1 *)
(* H |- x : 0 means the signal [e] is constant [x(t-h)] = x(t)] *)
(* 1/2 means it is smooth [x(t-h) ~ x(t)] for [h~0] *)
(* 1 - it may be discontinuous [x(t-h) !~ x(t)*)

(** Type definitions. *)

(* type scheme *)
type ti_scheme = 
    { typ_vars: t list; (* list of type variables *)
      typ_rel: (t * t list) list; (* the relation between variables *)
      typ_body: ti;        (* type of the result *)
    }

 and ti =
   | Ifun of ti * ti
   | Iproduct of ti list
   | Iatom of t

(* a smoothness type t is associated to its left types t_infs *)
(* and right types t_sups such that t_infs < t < t_sups *)
(* when t is minimal, alls its infimum can be replaced by itself *)
(* when t is maximal, all its supremum can be replaced by itself *)

and t =
    { mutable i_desc: desc; (* its descriptor *)
      mutable i_level: int; (* its level *)
      mutable i_index: int; (* a unique ident associated to the variable *)
      mutable i_inf: t list; (* infimun *)
      mutable i_sup: t list; (* supremum *)
      mutable i_useful: bool; (* is-it an intermediate variable ? *)
      mutable i_polarity: polarity; (* its polarity *)
      mutable i_visited: int; (* is-it visited already ? *)
    }

and desc = 
  | Ivalue of value
  | Ivar 
  | Ilink of t

and value = | Izero | Ihalf | Ione

and polarity = Punknown | Pplus | Pminus | Pplusminus

let compare i1 i2 = Stdlib.compare i1.i_index i2.i_index

let no_typ = Iproduct []

let scheme t = { typ_vars = []; typ_rel = []; typ_body = t }

(** An entry in the type environment *)
type tentry =
    { t_tys: ti_scheme; (* the type [t] of x *)
      t_last: t option; (* if [last x] is used, its smoothness *)
    }
