(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* causality types *)

(** Type definitions. *)

(* type scheme *)
type tc_scheme = 
    { typ_vars: t list; (* list of type variables *)
      typ_rel: (t * t list) list; (* the relation between variables *)
      typ: tc; (* type *)
    }

and tc =
  | Cfun of tc * tc
  | Cproduct of tc list (* products *)
  | Catom of t (* dependences *)

(* a causality variable points to its predecessors and successors *)
and t =
    { mutable c_desc: desc; (* its descriptor *)
      mutable c_level: int; (* its level *)
      mutable c_index: int; (* a unique ident associated to the variable *)
      mutable c_inf: t list; (* infimum *)
      mutable c_sup: t list; (* supremum *)
      mutable c_useful: bool; (* is-it an intermediate variable ? *)
      mutable c_polarity: polarity; (* its polarity *)
      mutable c_info: info option; (* a possible concrete name *)
      mutable c_visited: int; (* is-it visited already ? *)
    }

and desc =
  | Cvar
  | Clink of t

and info =
  | Cname of Ident.t
  | Clast of Ident.t

and polarity = Punknown | Pplus | Pminus | Pplusminus

(* only compare indexes. *)
let rec compare c1 c2 = Stdlib.compare c1.c_index c2.c_index 
    
let no_typ = Cproduct []
