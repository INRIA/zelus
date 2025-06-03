(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Add a copy [lx] and an equation [lx = last*x]. Replace [last x] by [lx] *)
(* This pass is necessary for static scheduling. *)
(* This is done for every variable [x] for which [last x] is used *)
(* and that is neither an input, an output or a variable in a pattern matching *)

(*
  Example:

  local x, y, z init e
  do init x = v0 and init y = v1 and ... y = last x + 1 and
  ... x = last y + 1 and ... z ...

  is rewritten:

  local x, y, z init e do
  local lx, ly do
  init x = v0 and init y = v1 and ... lx = last* x ... y = lx + 1 and
  ... x = ly + 1 and ly = last* y and ... z ...
*)

open Zelus
open Ident

type 'a acc =
  { (* names that are defined locally as [local ... x ... do ... ] or *)
    (* [let [rec] ... x ... in ...] *)
    env: 'a Env.t; 
    (* if [x] is a local variable and [last x] is used in a expression *)
    (* then [last x] is replaced by [lx] and an equation [lx = last*x] is added. *)
    (* if [last* x] is used, it is left unchanged *)
    renaming: Ident.t Env.t; (* renaming [x -> lx] *)
  }

let empty = { env = Env.empty; renaming = Env.empty }

(* Make equations [lx1 = last* x1 and ... lxn = last* xn] *)
(* from a [renaming] where [renaming(x) = lx] *)
let add_lx_lastx l_renaming =
  let copy lx x = Aux.id_eq lx (Aux.last_star x) in
  Env.fold (fun x lx acc -> copy lx x :: acc) l_renaming []

(* add copy names [lx] to [l_env] *)
let add_last_names_to_env l_env l_renaming =
  Env.fold (fun x lx acc -> Env.add lx Typinfo.no_ienv acc) l_renaming l_env

(* add copy names [lx] to [vardec_list] *)
let add_last_names_to_vardec_list vardec_list l_renaming =
  Env.fold (fun x lx acc -> Aux.id_vardec lx :: acc) l_renaming vardec_list

let intro ({ env; renaming } as acc) id =
  try
    let lx = Env.find id renaming in lx, acc
  with
  | Not_found ->
     let lx = fresh "lx" in lx, { acc with renaming = Env.add id lx renaming }
                                   
(* add extra equations [lx = last* x] *)
let add_lx_lastx_to_leq ({ renaming } as acc) ({ l_eq; l_env; l_rec } as leq) =
  let l_renaming, renaming =
    Env.partition (fun x v -> Env.mem x l_env) renaming in
  let l_env = add_last_names_to_env l_env l_renaming in
  let l_rec = l_rec || not (Env.is_empty l_renaming) in
  (* for every [x] in [local_renaming] add an equatoin [lx = last*x] *)
  let l_eq = Aux.par (l_eq :: add_lx_lastx l_renaming) in
  { leq with l_eq; l_env; l_rec }, { acc with renaming }

let add_lx_lastx_to_block ({ renaming } as acc) ({ b_vars; b_body; b_env } as b) =
  let l_renaming, renaming =
    Env.partition (fun x v -> Env.mem x b_env) renaming in
  let b_env = add_last_names_to_env b_env l_renaming in
  let b_vars = add_last_names_to_vardec_list b_vars l_renaming in
  let b_body = Aux.par (b_body :: add_lx_lastx l_renaming) in
  { b with b_vars; b_body; b_env }, { acc with renaming }

(* replace every occurrence of [last x] where [x] is a local variable *)
(* by [lx]; an equation [lx = last*x] will be added. *)
let expression funs ({ env } as acc) ({ e_desc } as e) =
  match e_desc with
  | Elast { copy; id } ->
     if Env.mem id env then
       if copy then
         let lx, acc = intro acc id in
         (* turn [last x] into [lx] *)
         Aux.var lx, acc
       else e, acc
     else
       e, acc
  | Elet({ l_env } as leq, e) ->
     let leq, acc = Mapfold.leq_it funs { acc with env = Env.append l_env env } leq in
     let { renaming } = acc in
     let l_ = Env.to_list renaming in
     let e, acc = Mapfold.expression_it funs acc e in
     let leq, acc = add_lx_lastx_to_leq acc leq in
     { e with e_desc = Elet(leq, e) }, acc
  | Elocal({ b_env } as b, e) ->
     let b, acc = Mapfold.block_it funs { acc with env = Env.append b_env env } b in
     let e, acc = Mapfold.expression_it funs acc e in
     let { renaming } = acc in
     let l_ = Env.to_list renaming in
     let b, acc = add_lx_lastx_to_block acc b in
     { e with e_desc = Elocal(b, e) }, acc
  | _ ->
     Mapfold.expression funs acc e

let equation funs ({ env } as acc) ({ eq_desc } as eq) =
  match eq_desc with
  | EQlet({ l_env } as leq, eq) ->
     let leq, acc = Mapfold.leq_it funs { acc with env = Env.append l_env env } leq in
     let eq, acc = Mapfold.equation_it funs acc eq in
     let { renaming } = acc in
     let l_ = Env.to_list renaming in
     let leq, acc = add_lx_lastx_to_leq acc leq in
     { eq with eq_desc = EQlet(leq, eq) }, acc
  | EQlocal({ b_env } as b) ->
     let b, acc = Mapfold.block_it funs { acc with env = Env.append b_env env } b in
     let b, acc = add_lx_lastx_to_block acc b in
     let { renaming } = acc in
     let l_ = Env.to_list renaming in
     { eq with eq_desc = EQlocal(b) }, acc
  | _ -> Mapfold.equation funs acc eq

let pattern funs acc p = p, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs  in
  let funs =
    { Mapfold.defaults with pattern; expression; equation;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
