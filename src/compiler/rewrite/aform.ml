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
(* for any variable [x: t1 *...* t2n, introduce fresh names *)
(* [x1:t1,...,xn:tn] so that [x = (x1,...,xn)] *)
(* distribute pattern matchings [(p1,...,pn) = (e1,...,en)] into *)
(* p1 = e1 and ... pn = en] *)
open Ident
open Zelus
open Deftypes

let unbound x =
  Misc.internal_error "A-normal form" Ident.fprint_t x

type 'a tree = | Leaf of 'a | Lpar of 'a tree list

(* the type of the accumulator *)
type acc =
  { renaming: Ident.t Env.t; (* renaming environment *)
    subst: Ident.t tree Env.t;
  }

let empty = { renaming = Env.empty; subst = Env.empty }

(* matching. Translate [(p1,...,pn) = (e1,...,en)] into *)
(* [p1 = e1 and ... and pn = en] *)
let rec matching eq_list ({ pat_desc } as p) ({ e_desc } as e) =
  match pat_desc, e_desc with
    | Etuplepat(p_list), Etuple(e_list) ->
        List.fold_left2 matching eq_list p_list e_list
    | _ -> (Aux.eq_make p e) :: eq_list 

let find { renaming; subst } id =
  try Env.find id renaming with | Not_found -> unbound id

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

let var_ident global_funs acc id = find acc id, acc

(* Build an accumulator from an environment *)
let build global_funs ({ renaming; subst } as acc) env =
  let rec buildrec n ({ t_tys = { typ_body }; t_sort; t_path } as entry)
    (env, acc) =
    match t_sort with
    | Sort_val | Sort_var ->
       let t, env = value n entry env typ_body in
       env, { acc with subst = Env.add n t subst }
    | _ ->
       (* state variables are not splitted but simply renamed *)
       let m = Ident.fresh (Ident.source n) in
       Env.add m entry env,
       { acc with renaming = Env.add n m renaming }
  and value n entry env { t_desc } =
    (* produce a tree according to the structure of [t_desc] *)
    match t_desc with
      | Tvar | Tarrow _ | Tvec _ | Tconstr _ ->
         let m = Ident.fresh (Ident.source n) in
         Leaf(m), Env.add m entry env
      | Tproduct(ty_list) ->
         let t_list, acc = Util.mapfold (value n entry) env ty_list in
         Lpar(t_list), env
      | Tlink(ty_link) -> value n entry env ty_link in
  let env, acc = Env.fold buildrec env (Env.empty, acc) in
  env, acc

let pattern funs ({ renaming; subst } as acc) ({ pat_desc } as p) =
  match pat_desc with
  | Evarpat(x) -> 
     let p =
       try { p with pat_desc = Evarpat(Env.find x renaming) }
       with
       | Not_found ->
          try
            make_pat (Env.find x subst)
          with | Not_found -> unbound x in
     p, acc
  | _ -> raise Mapfold.Fallback

let expression funs ({ renaming; subst } as acc) ({ e_desc } as e) =
  match e_desc with
  | Evar(x) ->
     let e =
       try { e with e_desc = Evar(Env.find x renaming) }
       with
       | Not_found ->
          try
            make_exp (Env.find x subst)
          with | Not_found -> unbound x in
     e, acc
  | _ -> raise Mapfold.Fallback

let equation funs acc eq =
  let ({ eq_desc } as eq), acc = Mapfold.equation funs acc eq in
  let eq = match eq_desc with
    | EQeq(p, e) ->
       Aux.par (matching [] p e)
    | _ -> eq in
  eq, acc

let vardec_list funs ({ renaming; subst } as acc) v_list =
  (* Warning. if [n] is a state variable or associated with a *)
  (* default value of combine function, it is not split into a tuple *)
  (* but a single name. The code below makes this assumption. *)
  let vardec v_list ({ var_name } as v) =
    let n_list =
      try [Env.find var_name renaming]
      with Not_found ->
        try names [] (Env.find var_name subst) with Not_found -> unbound var_name in
    List.fold_left
      (fun v_list n -> { v with var_name = n } :: v_list) v_list n_list in
  List.fold_left vardec [] v_list, acc
  
let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with
      pattern; expression; equation; vardec_list;
      set_index; get_index; global_funs } in
  let p, _ = Mapfold.program_it funs empty p in
  p

