(***********************************************************************)
(*                                                                     *)
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

(* useful functions *)

(* general iterators and functions *)
let optional f acc = function
  | None -> acc
  | Some x -> f acc x

let optional_with_default f default = function
  | None -> default
  | Some x -> f x

let optional_unit f acc = function
  | None -> ()
  | Some x -> f acc x

let optional_map f = function
  | None -> None
  | Some(x) -> Some(f x)

let optional_with_map f acc = function
  | None -> None, acc
  | Some(x) -> let x, acc = f acc x in Some(x), acc

let optional_get = function
  | Some x -> x
  | None   -> assert false

let is_opt = function
  | Some _ -> true | None -> false

let rec iter f = function
  | [] -> []
  | x :: l -> let y = f x in y :: iter f l

let fold f l = List.rev (List.fold_left f [] l)

let from i =
  let rec fromrec acc i =
    match i with
    | 0 -> acc
    | _ -> fromrec ( i :: acc) (i - 1) in
  fromrec [] i

let mapfold f acc l =
  let rec maprec acc = function
    | [] -> [], acc
    | x :: l ->
       let y, acc = f acc x in
       let l, acc = maprec acc l in
       y :: l, acc in
  maprec acc l

let mapfold2 f acc l1 l2 =
  let rec maprec acc l1 l2 =
    match l1, l2 with
    | [], [] -> [], acc
    | x :: l1, y :: l2 ->
       let z, acc = f acc x y in
       let l, acc = maprec acc l1 l2 in
       z :: l, acc
    | _ -> failwith "mapfold2" in
  maprec acc l1 l2

let mapfold_opt f acc l =
  let rec maprec acc = function
    | [] -> [], acc
    | x :: l ->
       let y_opt, acc = f acc x in
       let l, acc = maprec acc l in
       (match y_opt with None -> l | Some(y) -> y :: l), acc in
  maprec acc l

(* duplicate a value into a list *)
let rec list_of n v = if n = 0 then [] else v :: (list_of (n-1) v)

(* takes the first patterns of the list, except the last one *)
let rec firsts = function
    | [] -> assert false
    | [p] -> [], p
    | p :: l -> let head, tail = firsts l in p :: head, tail

(* execute only *)
let continue_if_not b x f = if b then x else f x
