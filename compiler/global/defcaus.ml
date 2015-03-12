(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* causality types *)

(** Type definitions. *)

(* type scheme *)
type typ_scheme = 
    { typ_vars: t list; (* list of type variables *)
      typ_args: typ list; (* type of the arguments *)
      typ_res: typ;       (* type of the result *)
    }

and typ =
    | Cproduct of typ list (* products *)
    | Catom of t (* dependences *)

(* a causality variable points to its predecessors and successors *)
and t =
    { mutable c_desc: desc; (* its descriptor *)
      mutable c_level: int; (* its level *)
      mutable c_index: int; (* a unique ident associated to the variable *)
      mutable c_sup: t list; (* supremum *)
      mutable c_useful: bool; (* is-it an intermediate variable ? *)
      mutable c_polarity: polarity; (* its polarity *)
      mutable c_info: info option; (* a possible concrete name *)
    }

and desc =
  | Cvar
  | Clink of t

and info =
  | Cname of Ident.t
  | Clast of Ident.t

and polarity = Punknown | Pplus | Pminus | Pplusminus

let compare c1 c2 = Pervasives.compare c1.c_index c2.c_index

(** A module to represent sets of causality variables *)

type tentry = 
    { t_typ: typ;   (* the causality type of x *)
      t_last: bool; (* [last x] is allowed *)
    }

