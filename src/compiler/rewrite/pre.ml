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

(* Translation of fby/pre into init/last *)
(*
    [pre(e)] => [local x, (last m) do m = e and x = last* m in x]

    [e1 fby e2] => [local x, m init e1 do m = e2 and x = last* m in x]
*)

open Misc
open Location
open Deftypes
open Ident
open Zelus
open Aux
open Mapfold

let fresh_x () = fresh "x"
let fresh_m () = fresh "m"

(* two options - generates let/rec or local/in *)
(* [let rec m = e and x = last* m in x] *)
let let_mem_value e =
  let x = fresh_x () in
  let m = fresh_m () in
  Aux.e_letrec [Aux.id_eq m e; Aux.id_eq x (Aux.last_star m)] (var x)
    
(* [let rec init m = e1 and m = e2 and x = last* m in x] *)
let let_init_mem_value e1 e2 =
  let x = fresh_x () in
  let m = fresh_m () in
  Aux.e_letrec [Aux.eq_init m e1; Aux.id_eq m e2; Aux.id_eq x (Aux.last_star m)]
    (var x)

(* Defines a value [local x, (last m) do m = e and x = last* m in x] *)
let local_mem_value e =
  let x = fresh_x () in
  let m = fresh_m () in
  Aux.e_local (Aux.block_make [Aux.vardec x false None None;
                               Aux.vardec m true None None]
                 [Aux.id_eq m e; Aux.id_eq x (Aux.last_star m)]) (var x)

(* Defines a state variable with initialization *)
(* [local x, m init e1 do m = e2 and x = last* m in x] *)
let local_init_mem_value e1 e2 =
  let x = fresh_x () in
  let m = fresh_m () in
  Aux.e_local (Aux.block_make [Aux.vardec x false None None;
                               Aux.vardec m false (Some(e1)) None]
                 [Aux.id_eq m e2; Aux.id_eq x (Aux.last_star m)]) (var x)

(* Translation of expressions. *)
let expression funs acc e =
  let ({ e_desc } as e), acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eop(Efby, [e1; e2]) ->
     (* [let rec init m = e1 and m = e2 and x = last* m in x] *)
     local_init_mem_value e1 e2, acc
  | Eop(Eunarypre, [e1]) ->
     (* [let rec m = e1 and x = last* m in x] *)
     local_mem_value e1, acc
  | _ -> e, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs () p in
  { p with p_impl_list = p_impl_list }
