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

let fprint_ientry ff { cur; default } =
  match default with
  | Val ->
     Format.fprintf ff "@[{ cur = %a;@ default = Val }@]@," Output.value cur
  | Last(v) ->
     Format.fprintf ff "@[{ cur = %a;@ default = Last(%a) }@]@,"
       Output.value cur Output.value v
  | Default(v) ->
     Format.fprintf ff "@[{ cur = %a;@ default = Default(%a) }@]@,"
       Output.value cur Output.value v


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
   
let stop_at_location loc r_opt =
  if !set_verbose then
    match r_opt with
    | None ->
       Format.eprintf "%aTyping error.@."
         Location.output_location loc;
       raise Stdlib.Exit
    | Some _ -> r_opt
  else r_opt
