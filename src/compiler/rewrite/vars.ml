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

(* free variables, defined variables. Writes and env. must be correct *)
(* The definition below considers that [y] is free in *)
(* equation [...x... = ... y...]. *)

open Ident
open Zelus
open Mapfold

type acc = { bounded: S.t; current: S.t; last: S.t }

let empty = { bounded = S.empty; current = S.empty; last = S.empty }

let build global_funs ({ bounded } as acc) p_env =
  p_env,
  { acc with bounded = Env.fold (fun x _ acc -> S.add x acc) p_env bounded }

let var_ident global_funs ({ bounded; current; last } as acc) x =
  let current = if S.mem x bounded || S.mem x current
                then current else S.add x current in
  x, { acc with current }

let last_ident global_funs ({ bounded; last } as acc) ({ id } as l) =
  let last = if S.mem id bounded || S.mem id last
             then last else S.add id last in
  l, { acc with last }

let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQeq(_, e) | EQinit(_, e) -> 
     let _, acc = Mapfold.expression_it funs acc e in eq, acc
  | EQder { handlers; e_opt } ->
     let _, acc = Util.mapfold (Mapfold.present_handler_e_it funs) acc handlers in
     let e_opt, acc = 
       Util.optional_with_map (Mapfold.expression_it funs) acc e_opt in
     eq, acc
  | EQemit(_, e_opt) -> 
     let _, acc = Util.optional_with_map (Mapfold.expression_it funs) acc e_opt in
     eq, acc
  | _ -> raise Mapfold.Fallback

let funs =   
  let global_funs =
    { Mapfold.default_global_funs with build; var_ident; last_ident } in
  { Mapfold.defaults with global_funs; equation }

type t =
  { lv: S.t; (* last variables *)
    v: S.t; (* variables *)
  }

let pattern { lv; v } p =
  let _, { last; current } =
    Mapfold.pattern_it funs { empty with last = lv; current = v } p in
  { lv = last; v = current }

let expression { lv; v } e =
  let _, { last; current } =
    Mapfold.expression_it funs
      { empty with last = lv; current = v } e in
  { lv = last; v = current }

let equation eq =
  let _, { last; current } =
    Mapfold.equation_it funs empty eq in
  { lv = last; v = current }
