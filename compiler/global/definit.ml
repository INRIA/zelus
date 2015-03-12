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
(* initialization types *)

(** Type definitions. *)

(* type scheme *)
type styp = 
    { typ_vars: init list; (* list of type variables *)
      typ_args: typ list; (* type of the arguments *)
      typ_res: typ;       (* type of the result *)
    }

and typ =
    | Iproduct of typ list
    | Iatom of init

(* an initialization type t is associated to its left type t_left *)
(* and right type t_right such that t_inf < t < t_sup wich are *)
(* both minimal from the dependence point-of-view *)
(* every time t is replaced by a constant, we simplify t_inf and t_sup *)
(* w.r.t the following rules: 0,...,0 < 0 and 1 < 1,...,1 *)  
and init =
    { mutable i_desc: init_desc; (* its descriptor *)
      mutable i_level: int; (* its level *)
      mutable i_index: int; (* a unique ident associated to the variable *)
      mutable i_inf: init list; (* infimun *)
      mutable i_sup: init list; (* supremum *)
      mutable i_useful: bool; (* is-it an intermediate variable ? *)
      mutable i_polarity: polarity; (* its polarity *)
      mutable i_visited: int; (* is-it a variable on a dependency cycle ? *)
    }

and init_desc = 
    | Izero
    | Ione
    | Ivar 
    | Ilink of init

and polarity = Punknown | Pplus | Pminus | Pplusminus
