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

(* This pass is necessary for static scheduling. *)
(* For every local variable [x] that is not an input nor output *)
(* such that [last x] is used *)
(* add an equation [lx = last* x] and replace [last x] by [lx] *)

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
    (* if [x] is local and [last x] is used, [last x] is replaced by [lx] *)
    (* and an equation [lx = last*x] is added. *)
    renaming: Ident.t Env.t; (* renaming [x -> lx] *)
  }

let empty = { env = Env.empty; renaming = Env.empty }

(* Make equations [lx1 = last* x1 and ... lxn = last* xn] *)
(* from a [renaming] where [renaming(x) = lx] *)
let add_last_copy_eq l_renaming =
  let copy lx x = Aux.id_eq lx (Aux.last_star x) in
  Env.fold (fun x lx acc -> copy lx x :: acc) l_renaming []

(* add copy names in [l_env] *)
let add_last_names_in_env l_env l_renaming =
  Env.fold (fun x lx acc -> Env.add lx Typinfo.no_ienv acc) l_renaming l_env

(* Make an equation [let lx1 = last* x1 and ... lx_n = last* xn in eq] *)
let eq_let_lx_lastx l_renaming eq =
  if Env.is_empty l_renaming then eq
  else let eq_list = add_last_copy_eq l_renaming in
       Aux.eq_let (Aux.leq eq_list) eq

(* Inject [let lx1 = last* x1 and ... lx_n = last* xn in eq] into a block *)
let block_let_lx_lastx l_renaming ({ b_body } as b) =
  { b with b_body = eq_let_lx_lastx l_renaming b_body }

let intro ({ env; renaming } as acc) id =
  try
    let lx = Env.find id renaming in lx, acc
  with
  | Not_found ->
     let lx = fresh "lx" in lx, { acc with renaming = Env.add id lx renaming }
                                             
(* Given a [renaming] and an environment [l_env], decompose it in two *)
(* Returns [l_renaming] (for local renaming) and [r_renaming] (for *)
(* renaming that remains) such that [renaming = l_renaming + r_renaming] *)
(* [Names(l_renaming) subset Names(l_env)] *)
let extract_local_renaming l_env renaming =
  Env.fold
    (fun x lx (l_renaming, r_renaming) ->
       if Env.mem x l_env then Env.add x lx l_renaming, r_renaming
       else l_renaming, Env.add x lx r_renaming)
    renaming (Env.empty, Env.empty)
    
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
  | _ -> raise Mapfold.Fallback

(* add extra equations [lx = last* x] *)
let leq_t funs ({ env } as acc) ({ l_eq; l_env; l_rec } as leq) =
  let l_eq, { renaming } =
    Mapfold.equation_it
      funs { acc with env = Env.append l_env env } l_eq in
  (* add an equation [lx = last* x] for every [x\lx] in [renaming inter l_env] *)
  let l_renaming, renaming = extract_local_renaming l_env renaming in
  (* the resulting equations are recursive if [l_rec] or *)
  (* at least one copy is added *)
  let l_rec = l_rec || not (Env.is_empty l_renaming) in
  { leq with l_eq = Aux.par (l_eq :: add_last_copy_eq l_renaming);
             l_env = add_last_names_in_env l_env l_renaming; l_rec },
  { env; renaming }

let block funs acc ({ b_vars; b_body; b_env } as b) =
  let b_vars, ({ env } as acc) =
    Util.mapfold (Mapfold.vardec_it funs) acc b_vars in
  let b_body, ({ renaming } as acc) =
    Mapfold.equation_it
      funs { acc with env = Env.append b_env env } b_body in
  (* add extra equations [lx = last* x] *)
  let l_renaming, renaming = extract_local_renaming b_env renaming in
  { b with b_vars; b_body = eq_let_lx_lastx l_renaming b_body},
  { env; renaming }

let for_eq_t funs acc ({ for_out; for_block; for_out_env } as f) =
  let for_out, ({ env } as acc) =
    Util.mapfold (Mapfold.for_out_it funs) acc for_out in
  let ({ b_body } as for_block), ({ renaming } as acc) =
    Mapfold.block_it funs
      { acc with env = Env.append for_out_env env } for_block in
  (* add extra equations [lx = last* x] *)
  let l_renaming, renaming = extract_local_renaming for_out_env renaming in
  let for_block = { for_block with b_body = eq_let_lx_lastx l_renaming b_body } in
  { f with for_out; for_block }, { env; renaming }

let pattern funs acc p = p, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs  in
  let funs =
    { Mapfold.defaults with pattern; expression; leq_t; block;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
