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

(* Specialization of recursive size functions *)

(* declarations [let rec f1<<n1,...>> = ... and fk<<<n1,...>> = ...] *)
(* are removed. Fresh functions are introduced for all specialized applications *)
(* that is, f<<s1,...>> where [s1,...] is a list of constant values *)

open Misc
open Location
open Ident
open Zelus

(* memoization table; mapping [(id, s1,...,sn) -> id_j] *)
module Memo = 
  Map.Make 
    (struct 
      type t = Ident.t * int list 
      let compare (id1, l1) (id2, l2) =
        let v = Ident.compare id1 id2 in
        if v = 0 then Stdlib.compare l1 l2 else v
    end)

type acc =
  { memo: Ident.t Memo.t; (* memoization table *)
    new_fundef: (Ident.t * Typinfo.funexp) list; 
    (* list of new functions definitions *)
    env_of_sizefun: Typinfo.sizefun Env.t; 
    (* map of size functions [f -> <<n1,...>>.e] *)
    env_of_sizes: int Env.t;
  (* map of sizes [id -> v] with [v] a (positive) integer *)
  }

let empty = 
  { memo = Memo.empty; new_fundef = []; 
    env_of_sizefun = Env.empty; env_of_sizes = Env.empty }

let add_sizefun funs ({ env_of_sizefun } as acc) ({ sf_id } as sizefun) =
  { acc with env_of_sizefun = Env.add sf_id sizefun env_of_sizefun  }

let size env_of_size s = 42

let equation funs acc ({ eq_desc; eq_loc } as eq) =
  match eq_desc with
  | EQlet({ l_eq } as leq, eq_let) ->
     let eq_list, acc = 
       match Typing.eq_or_sizefun eq_loc l_eq with
       | Either.Left(eq_list) -> eq_list, acc
       | Either.Right(sizefun_list) ->
          [], List.fold_left (add_sizefun funs) acc sizefun_list in
     let eq_list, acc = Util.mapfold (Mapfold.equation_it funs) acc eq_list in
     let eq_let, acc = Mapfold.equation_it funs acc eq_let in
     { eq with eq_desc = EQlet({ leq with l_eq = Aux.par eq_list }, eq_let) }, acc
  | _ -> raise Mapfold.Fallback

let expression funs ({ memo; env_of_sizefun; env_of_sizes } as acc) 
      ({ e_desc; e_loc } as e) =
  match e_desc with
  | Elet({ l_eq } as leq, e_let) ->
     let eq_list, acc = 
       match Typing.eq_or_sizefun e_loc l_eq with
       | Either.Left(eq_list) -> eq_list, acc
       | Either.Right(sizefun_list) ->
          [], List.fold_left (add_sizefun funs) acc sizefun_list in
     let eq_list, acc = Util.mapfold (Mapfold.equation_it funs) acc eq_list in
     let e_let, acc = Mapfold.expression_it funs acc e_let in
     { e with e_desc = Elet({ leq with l_eq = Aux.par eq_list }, e_let) }, acc
  | Esizeapp { f = { e_desc = Evar(f) }; size_list } ->
     (* [f <<s1,...>>] where the [s_i] are immediate values] *)
     begin try
        let { sf_id; sf_id_list; sf_e; sf_loc; sf_env } as f =
          Env.find f env_of_sizefun in
        let v_list = List.map (size env_of_sizes) size_list in
        let f_id = Memo.find (sf_id, v_list) memo in
        { e with e_desc = Evar(f_id) }, acc
       with
         Not_found -> e, acc
     end
  | _ -> raise Mapfold.Fallback

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with
      global_funs; equation; expression; set_index; get_index; } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs empty p in
  { p with p_impl_list }
