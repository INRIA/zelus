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
    [pre(e)] => [let rec m = e in last* m]

    [e1 fby e2] => [let rec init m = e1 and m = e2 in last*m]
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

(* some auxiliary functions; not used for the moment *)
(* Defines a value [let x = e in e_let] *)
let let_value e =
  let x = fresh_x () in
  Aux.e_letrec [Aux.id_eq x e] (var x)

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


(* translation of [pre] and [fby] *)
let pre e =
  let m = fresh_m () in
  Aux.e_letrec [Aux.id_eq m e] (Aux.last_star m)
let fby e1 e2 =
  let m = fresh_m () in
  Aux.e_letrec [Aux.eq_init m e1; Aux.id_eq m e2] (Aux.last_star m)

(* Translation of expressions. *)
let expression funs acc e =
  let ({ e_desc } as e), acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eop(Efby, [e1; e2]) ->
     (* [let rec init m = e1 and m = e2 and x = last* m in x] *)
     fby e1 e2, acc
  | Eop(Eunarypre, [e1]) ->
     (* [let rec m = e1 and x = last* m in x] *)
     pre e1, acc
  | Eop(Eifthenelse, [e1; e2; e3]) ->
     (* if [e2] (and [e3]) is stateful, name the result *)
     let e2 = if Unsafe.expression e2 then let_value e2 else e2 in
     let e3 = if Unsafe.expression e3 then let_value e3 else e3 in
     { e with e_desc = Eop(Eifthenelse, [e1; e2; e3]) }, acc
  | Eop(Eup, [e1]) ->
     (* turns it into [let x = up(e1) in x] *)
     let_value e, acc
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
