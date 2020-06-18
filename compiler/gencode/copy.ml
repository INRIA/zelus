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

(* add a copy method which copies the state into a destination *)
(* [method copy dest] recursively copies the internal state into [dest] *)

open Misc
open Ident
open Lident
open Deftypes
open Obc
open Format

(* read/write of a state variable. *)
let state is_read v k =
  match k with
  | None -> v
  | Some(k) ->
     match k with
     | Deftypes.Cont ->
	Oleft_state_primitive_access(v, Ocont)
     | Deftypes.Zero ->
	Oleft_state_primitive_access
	  (v, if is_read then Ozero_in else Ozero_out)
     | Deftypes.Horizon | Deftypes.Period | Deftypes.Encore -> v

let copy_memory dest inst_list { m_name; m_typ; m_kind; m_size } =
  Oassign_state(state false (Oleft_state_name(dest)) m_kind,
		Ostate(state true Oself m_kind)) :: inst_list

let copy_instance dest inst_list { i_name; i_machine; i_size } =
  inst_list

let machine f ({ ma_memories; ma_instances; ma_methods } as mach) =
  let dest = Ident.fresh "dest" in
  { mach with
    ma_methods =
      { me_name = Ohorizon;
	me_params =
	  [Ovarpat(dest, Otypevar("'a"))];
	me_body =
	  Osequence(List.fold_left
		      (copy_memory dest)
		      (List.fold_left (copy_instance dest) [] ma_instances)
		      ma_memories);
	me_typ = Initial.typ_unit } :: ma_methods }
    
  (** The main entry. *)
let implementation impl =
  match impl with
  | Oletmachine(f, mach) -> 
     (* only continuous machines are concerned *)
     Oletmachine(f, machine f mach)
  | Oletvalue _ | Oletfun _ | Oopen _ | Otypedecl _ -> impl
									 
let implementation_list impl_list = Misc.iter implementation impl_list
