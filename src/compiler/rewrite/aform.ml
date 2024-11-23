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

(* A-normal form: distribution of tuples *)
(* for any variable [x: t] where [t] is a structured type *)
(* introduce fresh names [x1:t1,...,xn:tn] so that [t = (t1,...,tn)] *)
(* and recursively. Replace an equation [x = e] by [(x1,...,xn) = e] *)
(* and [p1,...,pn = e1,..., en] by [p1 = e1 and ... and [pn = en] *)
open Ident
open Zelus
open Deftypes

type 'a tree = | Leaf of 'a | Lpar of 'a tree list

(* the type of the accumulator *)
type acc =
  { subst: Ident.t tree Env.t; (* [x -> (x1, (x2, ...), ..., xn)] *)
  }

let empty = { subst = Env.empty }

(* matching. Translate [(p1,...,pn) = (e1,...,en)] into *)
(* [p1 = e1 and ... and pn = en] *)
let rec matching eq_list ({ pat_desc } as p) ({ e_desc } as e) =
  match pat_desc, e_desc with
    | Etuplepat(p_list), Etuple(e_list) ->
        List.fold_left2 matching eq_list p_list e_list
    | _ -> (Aux.eq_make p e) :: eq_list 

let find { subst } id =
  try
    let t = Env.find id subst in
    let id = match t with | Leaf(id) -> id | Lpar _ -> assert false in id
  with | Not_found -> id

let rec make_pat t =
  match t with
  | Leaf(id) -> Aux.varpat id
  | Lpar(t_list) -> Aux.tuplepat (List.map make_pat t_list)

let rec make_exp t =
  match t with
  | Leaf(id) -> Aux.var id
  | Lpar(t_list) -> Aux.tuple (List.map make_exp t_list)

let rec names acc t =
  match t with
  | Leaf(id) -> id :: acc
  | Lpar(t_list) -> List.fold_left names acc t_list

(* Build an accumulator from an environment *)
let build global_funs ({ subst } as acc) env =
  let rec buildrec n ({ t_tys = { typ_body }; t_sort } as entry)
    (env, acc) =
    match t_sort with
    | Sort_val | Sort_var ->
       let t, env = value n entry env typ_body in
       env, { subst = Env.add n t subst }
    | _ ->
       (* state variables are not decomposed *)
       Env.add n entry env, acc
  and value
    n ({ t_tys = { typ_vars } } as entry) env ({ t_desc } as typ_body) =
    (* produce a tree according to the structure of [t_desc] *)
    match t_desc with
      | Tvar | Tarrow _ | Tvec _ | Tconstr _ ->
         let m = Ident.fresh (Ident.source n) in
         Leaf(m), Env.add m { entry with t_tys = { typ_vars; typ_body } } env
      | Tproduct(ty_list) ->
         let t_list, acc =
           Util.mapfold (value n entry) env ty_list in
         Lpar(t_list), env
      | Tlink(ty_link) -> value n entry env ty_link in
  let env, acc = Env.fold buildrec env (Env.empty, acc) in
  env, acc

let pattern funs ({ subst } as acc) ({ pat_desc } as p) =
  match pat_desc with
  | Evarpat(x) -> 
     let p = try make_pat (Env.find x subst) with Not_found -> p in
     p, acc
  | _ -> raise Mapfold.Fallback

let expression funs ({ subst } as acc) ({ e_desc } as e) =
  match e_desc with
  | Evar(x) ->
     let e = try make_exp (Env.find x subst) with Not_found -> e in
     e, acc
  | _ -> raise Mapfold.Fallback

let equation funs acc eq =
  let ({ eq_desc } as eq), acc = Mapfold.equation funs acc eq in
  let eq = match eq_desc with
    | EQeq(p, e) ->
       Aux.par (matching [] p e)
    | _ -> eq in
  eq, acc
 
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build } in
  let funs =
    { Mapfold.defaults with
      pattern; expression; equation;
      set_index; get_index; global_funs } in
  let p, _ = Mapfold.program_it funs empty p in
  p

