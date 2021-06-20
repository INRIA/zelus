(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Misc
open Ident

let print_message comment =
  if !set_verbose then
    Format.eprintf "@[%s (env): @,@]@\n" comment 

let print_program impl_list =
  if !set_verbose then
    (* let err_ff = Format.formatter_of_out_channel stderr in
    Printer.program err_ff impl_list *) ()
