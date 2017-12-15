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
(* initialization types *)

(** Type definitions. *)

(* type scheme *)
type ti_scheme = 
    { typ_vars: t list; (* list of type variables *)
      typ: ty;        (* type of the result *)
    }

 and ty =
   | Ifun of ty * ty
   | Iproduct of ty list
   | Iatom of t

(* an initialization type t is associated to its left type t_left *)
(* and right type t_right such that t_inf < t < t_sup wich are *)
(* both minimal from the dependence point-of-view *)
(* every time t is replaced by a constant, we simplify t_inf and t_sup *)
(* w.r.t the following rules: 0,...,0 < 0 and 1 < 1,...,1 *)  
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
  | Izero
  | Ione
  | Ivar 
  | Ilink of t

and polarity = Punknown | Pplus | Pminus | Pplusminus

let compare i1 i2 = Pervasives.compare i1.i_index i2.i_index
