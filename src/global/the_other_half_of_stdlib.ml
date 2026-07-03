(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2026 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(** Most languages have this thing called a standard library *)
(** Alas, this is OCaml... *)


(** https://hackage-content.haskell.org/package/base/docs/Data-List.html *)
(** Extract the last element of a list. *)
(** The list must be non-empty. *)
let last (list: 'a list): 'a = list |> List.rev |> List.hd

(** https://hackage-content.haskell.org/package/base/docs/Data-List.html *)
(** Return all the elements of a list except the last one. *)
(** The list must be non-empty. *)
let init (list: 'a list): 'a list = list |> List.rev |> List.tl |> List.rev

(** https://hackage-content.haskell.org/package/base/docs/Data-List.html *)
(** Return a prefix of length n of a list. *)
(** The list must of length at least n. *)
let rec take (n: int) (list: 'a list): 'a list =
  if n > 0 then
    match list with
    | [] -> failwith "Not enough elements in list"
    | x :: xs -> x :: (take (n - 1) xs)
  else []

(** https://doc.rust-lang.org/std/option/enum.Option.html#method.map_or *)
(** Returns the provided default result (if none), *)
(** or applies a function to the contained value (if any). *)
let map_or (f: 'a -> 'b) (default: 'b) (opt: 'a option): 'b =
  opt |> Option.map f |> Option.value ~default

(** https://doc.rust-lang.org/std/option/enum.Option.html#method.ok_or *)
(** Returns the contained value or raises the provided exception *)
let unwrap_or_raise (err: exn) (opt: 'a option) =
  match opt with
  | Some x -> x
  | None -> raise err
