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

type kind =
  | Etype : kind (* type error for values *)
  | Estate : kind (* type error for states *)
  | Eunbound_ident : Ident.t -> kind (* unbound variable *)
  | Eunbound_lident : Lident.t -> kind (* unbound global variable *)
  | Eshould_be_last : Ident.t -> kind 
  (* [x] should be a state variable with last *)
  | Eshould_be_node : Lident.t  -> kind (* [x] should be a node *)
  | Eshould_be_value : Lident.t  -> kind (* [x] should be a value *)
  | Eand_non_linear : Ident.t  -> kind (* [x] appears twice *)
  | Eno_default : Ident.t -> kind (* no default value is given to [x] *)
  | Einitial_state_with_parameter : Ident.t  -> kind 
  | Eassert_false : kind (* an error that should not appear; [= assert false] *)
  | Euncausal : kind (* some bottom value remain *)
  | Euninitialised : kind (* some nil value remain *)
                       
type t = Location.t * kind

let error loc kind = Error (loc, kind)
