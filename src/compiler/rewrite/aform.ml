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
       
(* the type of the accumulator *)
type acc =
  { renaming: Ident.t Env.t; (* renaming environment *)
    env: (Typinfo.pattern * Typinfo.exp) Env.t;
  }
  
(* Build a renaming from an environment *)
let build global_funs ({ renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }

(* associate a pattern and an expression to a variable according to its type *)
(* [intro t_env subst = subst', t_env'] *)
let build global_funs ({ renaming; env } as acc) env =
  let rec value entry acc ({ t_desc } as ty) =
    match t_desc with
    | Tvar | Tarrow _ | Tvec _ | Tconstr _ -> result entry acc ty
    | Tproduct(ty_list) ->
       let p_e_list, acc = Util.mapfold (value entry) acc ty_list in
       let p_list, e_list = List.split p_e_list in
       Aux.tuplepat p_list, Aux.tuple e_list, acc
    | Tlink(ty_link) ->
       value entry acc ty_link in
  and result n entry acc ty =
    let m = Ident.fresh (Ident.source n) in
    (Aux.varpat m, Aux.var m),
    Env.add n { entry with t_tys = Deftypes.scheme ty } acc in
    let buildrec n ({ t_tys = { typ_body }; t_sort; t_path } as entry)
          (env, renaming) =
    let pat, e = intro_from_typ m = Ident.fresh (Ident.source n) in
    
  (* returns a pair [spat, se] with [spat] a pattern, [se] an expression *)
  let result { source } entry acc ty =
    let id = Ident.fresh source in
    (Aux.varpat id, Aux.var id),
    Env.add id { entry with t_tys = Deftypes.scheme ty } acc in
  let rec value id entry acc ({ t_desc } as ty) =
    match t_desc with
    | Tvar | Tarrow _ | Tvec _ | Tconstr _ -> result id entry acc ty
    | Tproduct(ty_list) ->
       let p_e_list, acc = Util.mapfold (value id entry) acc ty_list in
       let p_list, e_list = List.split p_e_list in
       (Aux.tuplepat p_list, Aux.tuple e_list), acc
    | Tlink(ty_link) -> value id entry acc ty_link in
  let add id ({ t_tys = { typ_body }; t_sort; t_path } as entry) (subst_acc, env_acc) =
    match t_sort with
    | Sort_val | Sort_var ->
	let r, env_acc = value id entry env_acc typ_body in
	Env.add id r subst_acc, env_acc
    | _ ->
     (* state variables are not splitted but renamed *)
     let r, env_acc = result id entry env_acc typ_body in
     Env.add id r subst_acc, env_acc in
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }Env.fold add t_env (subst, Env.empty)

(* matching. Translate [(p1,...,pn) = (e1,...,en)] into the set of *)
(* equations [p1 = e1 and ... and pn = en] *)
(* [compose] defines the type of equation: [init p = e] or [p = e] *)
let rec matching compose eq_list ({ pat_desc } as p) ({ e_desc } as e) =
  match pat_desc, e_desc with
    | Etuplepat(p_list), Etuple(e_list) ->
        matching_list compose eq_list p_list e_list
    | _ -> (compose p e) :: eq_list

and matching_list compose eq_list p_list e_list =
  List.fold_left2 (matching compose) eq_list p_list e_list

let matching p_list e_list =
  List.map2 (fun p e -> Aux.eq p e) p_list e_list

let equation funs acc ({ eq_desc } as eq) =
  let eq, acc = Mapfold.equation funs acc eq in
  let desc = match eq_desc with
  | EQeq(p, e) -> 
     let eq_list = matching p e in
     EQand { ordered = false; eq_list }
  | _ -> eq_desc in
  { eq with eq_desc }, acc
     
let block funs acc ({ b_vars; b_body; b_env } as b) =
  
  let vardec_list subst v_list =
  (* Warning. if [n] is a state variable or associated with a *)
  (* default value of combine function, it is not split into a tuple *)
  (* but a single name. The code below makes this assumption. *)
  let vardec acc ({ vardec_name = n} as v) =
    let p = pat_of_name n subst in
    let nset = Vars.fv_pat S.empty S.empty p in
    S.fold (fun n acc -> { v with vardec_name = n } :: acc) nset acc in
  List.fold_left vardec [] v_list in
  
 let subst, b_env = build b_env subst in
  let v_list = vardec_list subst v_list in
  { b with b_vars = v_list; b_body = equation_list subst eq_list;
	   b_env = b_env; b_write = Deftypes.empty }

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> impl
    | Econstdecl(n, is_static, e) ->
       { impl with desc = Econstdecl(n, is_static, expression Env.empty e) }
    | Efundecl(n, ({ f_body = e; f_env = f_env; f_args = p_list } as body)) ->
       let subst, f_env = build f_env Env.empty in
       let p_list = List.map (pattern subst) p_list in
       let e = expression subst e in
       { impl with desc =
		     Efundecl(n, { body with f_body = e;
					     f_env = f_env; f_args = p_list }) }

let implementation_list impl_list = Zmisc.iter implementation impl_list

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with
      expression; global_funs; set_index; get_index; implementation; 
      open_t } in
  let p, _ = Mapfold.program_it funs { empty with genv } p in
  p

