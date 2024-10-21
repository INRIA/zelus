(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Zelus
open Monad
open Find
open Primitives

(* values for records *)
let record_access { label; arg } =
  (* look for [label] in the value of [arg] *)
  let open Opt in
  let* record_list = get_record arg in
  let rec find l record_list =
    match record_list with
    | [] -> none
    | { label; arg } :: record_list ->
       if label = l then return arg
       else find l record_list in
  find label record_list

let record_with label_arg_list ext_label_arg_list =
  let open Opt in
  (* inject {label; arg} into a record *)
  let rec inject label_arg_list l arg =
    match label_arg_list with
    | [] -> none
    | { label } as entry :: label_arg_list ->
       if label = l then return ({ label; arg } :: label_arg_list)
       else let* label_arg_list = inject label_arg_list l arg in
            return (entry :: label_arg_list) in
  (* join the two *)
  let rec join label_arg_list ext_label_arg_list =
    match ext_label_arg_list with
    | [] -> return label_arg_list
    | { label; arg } :: ext_label_arg_list ->
       let* label_arg_list = inject label_arg_list label arg in
       join label_arg_list ext_label_arg_list in
  join label_arg_list ext_label_arg_list
