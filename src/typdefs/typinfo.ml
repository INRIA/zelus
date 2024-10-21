(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* type annotations for terms *)

type info =
  { t_typ: Deftypes.typ;
    t_caus: Defcaus.tc;
    t_init: Definit.ti }

type ienv = Deftypes.typentry

type pattern = info Zelus.pattern
type exp = (info, ienv) Zelus.exp
type eq = (info, ienv) Zelus.eq

let no_info =
  { t_typ = Deftypes.no_typ;
    t_caus = Defcaus.no_typ;
    t_init = Definit.no_typ }

let no_ienv =
  Deftypes.entry (Deftypes.Tfun(Tany))
    Deftypes.Sort_val (Deftypes.scheme Deftypes.no_typ)

let set_type typinfo ty = { typinfo with t_typ = ty }
let set_caus typinfo tc = { typinfo with t_caus = tc }
let set_init typinfo ti = { typinfo with t_init = ti }

let get_type { t_typ } = t_typ
