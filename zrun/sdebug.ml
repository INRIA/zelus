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

open Misc
open Ident
open Value

let fprint_ientry ff { cur; last; default } =
  let value ff v =
    match v with
    | None -> Format.fprintf ff "none" | Some(v) -> Output.value ff v in
  Format.fprintf ff "@[{ cur = %a;@ last = %a;@ default = %a }@]@,"
    Output.value cur value last value default

let print_number comment n =
  if !set_verbose then Format.eprintf "@[%s %d@]@\n" comment n
  
let fprint_ienv comment ff env =
  Format.fprintf ff
      "@[%s (env): @,%a@]@\n" comment (Env.fprint_t fprint_ientry) env

let print_ienv comment env =
  if !set_verbose then Format.eprintf "%a" (fprint_ienv comment) env

let print_message comment =
  if !set_verbose then
    Format.eprintf "@[%s (env): @,@]@\n" comment 
