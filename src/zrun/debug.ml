(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2026 Inria Paris                                          *)
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

module Printer = Printer.Make(Noinfo)

let print_message comment =
  if !verbose then Format.fprintf Format.err_formatter "@[%s@]@." comment 

let fprint_ientry ff { cur; last; default; reinit } =
  let value ff v =
    match v with
    | None -> Format.fprintf ff "none" | Some(v) -> Output.value ff v in
  Format.fprintf ff "@[{ cur = %a;@ last = %a;@ default = %a; %s }@]@,"
    value cur value last value default (if reinit then "reinit" else "")

let print_number comment n =
  if !debug then Format.eprintf "@[%s %d@]@\n" comment n

let print_string comment s =
  if !debug then Format.eprintf "@[%s %s@]@\n" comment s

let fprint_ienv comment ff env =
  Format.fprintf ff
      "@[%s (env): @,%a@]@\n" comment (Env.fprint_t fprint_ientry) env

let print_ienv comment env =
  (* let l = Env.bindings env in *)
  flush stderr; flush stdout;
  if !debug then Format.eprintf "%a" (fprint_ienv comment) env;
  flush stderr; flush stdout

let do_if f x = if !debug then f x

  let print_state comment s =
  if !debug then Format.eprintf "%s: %a@." comment Output.pstate s  

let print_program p =
  if !verbose then Printer.program Format.err_formatter p

let incr_total_number_of_iterations_in_fixpoints n =
  if !Misc.compute_total_number_of_iterations_in_fixpoints
  then Misc.incr_total_number_of_iterations_in_fixpoints n
let reset_total_number_of_iterations_in_fixpoints () =
  if !Misc.compute_total_number_of_iterations_in_fixpoints
  then Misc.reset_total_number_of_iterations_in_fixpoints ()
let print_total_number_of_iterations_in_fixpoints () =
  if !Misc.compute_total_number_of_iterations_in_fixpoints then
    Format.eprintf
      "The total number of iterations for fixpoint computation is: %d\n"
      !Misc.total_number_of_iterations_in_fixpoints 

let print_nothing _ = ()

let counter = ref 0
let init_counter() = counter := 0
let incr_counter() = counter := !counter + 1
let print_counter() = Format.eprintf "Counter = %d\n" !counter
