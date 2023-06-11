(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2023 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* types.ml : basic operations over types *)

open Misc
open Ident
open Lident
open Deftypes
open Global
open Modules
open Zelus
open Genames
   
(* making types *)
let make ty =
  { t_desc = ty; t_level = generic; t_index = symbol#name }
let product ty_list =
  make (Tproduct(ty_list))
let vec ty e = make (Tvec(ty, e))
let const v = make (Sconst(v))
let size is_singleton si = make (Tsize(is_singleton, si))
let op o si1 si2 = make (Sop(o, si1, si2))
let arrowtype k ty_arg ty_res =
  make (Tarrow(k, ty_arg, ty_res))
let rec arrowtype_list k ty_arg_list ty_res =
  match ty_arg_list with
  | [] -> ty_res
  | ty :: ty_arg_list ->
     arrowtype k ty (arrowtype_list k ty_arg_list ty_res)
                  
let constr name ty_list abbrev = make (Tconstr(name, ty_list, abbrev))
let nconstr name ty_list = constr name ty_list (ref Tnil)

let new_size_var () =
  { t_desc = Svar; t_level = !binding_level; t_index = symbol#name }
let new_generic_size_var () =
  { t_desc = Svar; t_level = generic; t_index = symbol#name }

let new_var () =
  { t_desc = Tvar; t_level = !binding_level; t_index = symbol#name }
let new_generic_var () =
  { t_desc = Tvar; t_level = generic; t_index = symbol#name }
let rec new_var_list n =
  match n with
    0 -> []
  | n -> (new_var ()) :: new_var_list (n - 1)
let forall l typ_body = { size_vars = []; typ_vars = l; typ_body = typ_body }

			    
(* typing errors *)
exception Unify

let run_type expected_k =
  let ty_arg = new_var () in
  let ty_res = new_var () in
  arrowtype expected_k ty_arg ty_res
							      
(* shortening types *)
let rec typ_repr ty =
  match ty.t_desc with
    | Tlink(ty_son) ->
        let ty_son = typ_repr ty_son in
          ty.t_desc <- Tlink(ty_son);
          ty_son
    | _ -> ty

(* occur check and level modification *)
let occur_check level index ty =
  let rec check ty =
    match ty.t_desc with
    | Tvar ->
       if ty == index
       then raise Unify
       else if ty.t_level > level then ty.t_level <- level
    | Tproduct(ty_list) -> List.iter check ty_list
    | Tconstr(name, ty_list, _) ->
       List.iter check ty_list
    | Tarrow(_, ty_arg, ty_res) -> check ty_arg; check ty_res
    | Tsize _ -> ()
    | Tvec(ty, _) -> check ty
    | Tlink(link) -> check link
  in check ty

(* generalisation and non generalisation of a type. *)
(* the level of generalised type variables *)
(* is set to [generic] when the flag [is_gen] is true *)
(* and set to [!binding_level] when the flag is false *)
(* returns [generic] when a sub-term can be generalised *)
let list_of_typ_vars = ref []

let rec gen_ty is_gen ty =
  let ty = typ_repr ty in
  begin
    match ty.t_desc with
    | Tvar ->
       if ty.t_level > !binding_level
       then if is_gen
	    then (ty.t_level <- generic;
		  list_of_typ_vars := ty :: !list_of_typ_vars)
	    else ty.t_level <- !binding_level
    | Tproduct(ty_list) ->
       ty.t_level <-
         List.fold_left (fun level ty -> min level (gen_ty is_gen ty))
			notgeneric ty_list
    | Tconstr(name, ty_list, _) ->
       ty.t_level <- List.fold_left
		       (fun level ty -> min level (gen_ty is_gen ty))
		       notgeneric ty_list
    | Tarrow(_, ty_arg, ty_res) ->
	     ty.t_level <-
	       min (gen_ty is_gen ty_arg) (gen_ty is_gen ty_res)
    | Tsize _ -> ()
    | Tvec(ty, si) ->
       ty.t_level <- gen_ty is_gen ty
    | Tlink(link) ->
       ty.t_level <- gen_ty is_gen link
  end;
  ty.t_level

(* main generalisation function *)
let gen non_expensive typ_body =
  list_of_typ_vars := [];
  ignore (gen_ty non_expensive typ_body);
  { size_vars = []; typ_vars = !list_of_typ_vars; typ_body = typ_body }

let s = ref []
let save v = s := v :: !s
let cleanup () = List.iter (fun ty -> ty.t_desc <- Tvar) !s;
  s := []

(* makes a copy of a type *)
let rec copy ty =
  let level = ty.t_level in
   match ty.t_desc with
    | Tvar ->
      if level = generic
      then
        let v = new_var () in
        ty.t_desc <- Tlink(v);
        save ty;
        v
      else ty
    | Tlink(link) ->
        if level = generic
        then link
        else copy link
    | Tproduct(ty_list) ->
        if level = generic
        then
          product (List.map copy ty_list)
        else ty
    | Tconstr(name, ty_list, abbrev) ->
        if level = generic
        then
          constr name (List.map copy ty_list) abbrev
        else ty
    | Tarrow(k, ty_arg, ty_res) ->
       if level = generic
       then arrowtype k (copy ty_arg) (copy ty_res)
       else ty
    | Tsize(is_singleton, si) ->
       if level = generic
       then size is_singleton si
       else ty
    | Tvec(ty, si) ->
       if level = generic then vec (copy ty) si
       else ty
      
(* instanciation *)
let instance_of_type { typ_body = typ_body } =
  let typ_body = copy typ_body in
  cleanup ();
  typ_body

let instance_and_vars_of_type { typ_vars = typ_vars; typ_body = typ_body } =
  let typ_body = copy typ_body in
  let typ_vars = List.map typ_repr typ_vars in
  cleanup ();
  { typ_instance = typ_vars }, typ_body

let constr_instance
    { constr_arg = ty_list; constr_res = ty_res; constr_arity = n } =
  let ty_list = List.map copy ty_list in
  let ty_res = copy ty_res in
    cleanup ();
    { constr_arg = ty_list; constr_res = ty_res; constr_arity = n }

let label_instance { label_arg = ty_arg; label_res = ty_res } =
  let ty_arg = copy ty_arg in
  let ty_res = copy ty_res in
    cleanup ();
    { label_arg = ty_arg; label_res = ty_res }

let subst ty_var ty =
  match ty_var.t_desc with
  | Tvar -> ty_var.t_desc <- Tlink(ty)
  | _ -> assert false

let abbreviation q abbrev ty_list =
  let { info = ty_desc } = find_type (Modname q) in
  let find q =
      match ty_desc.type_desc with
      | Abbrev(ty_list, ty) -> ty_list, ty
      | _ -> raise Not_found in
  let arg_list, ty =
      match !abbrev with
      | Tnil ->
         let (arg_list, ty) = find q in
         abbrev := Tcons(arg_list, ty);
         (arg_list, ty)
      | Tcons(arg_list, ty) -> arg_list, ty in
    
    let new_arg_list = List.map copy arg_list in
    let new_ty = copy ty in
    cleanup ();
    List.iter2 subst new_arg_list ty_list;
    new_ty


(* same constructed types *)
let same_types n1 n2 = (n1 = n2)

(* unification *)
let rec unify expected_ty actual_ty =
  if expected_ty == actual_ty then ()
  else
    let expected_ty = typ_repr expected_ty in
    let actual_ty = typ_repr actual_ty in
      if expected_ty == actual_ty then ()
      else
        match expected_ty.t_desc, actual_ty.t_desc with
        |  Tvar, _ ->
            occur_check expected_ty.t_level expected_ty actual_ty;
            expected_ty.t_desc <- Tlink(actual_ty)
        | _, Tvar ->
           occur_check actual_ty.t_level actual_ty expected_ty;
           actual_ty.t_desc <- Tlink(expected_ty)
	| Tproduct(l1), Tproduct(l2) ->
           begin try
               List.iter2 unify l1 l2
             with
             | Invalid_argument _ -> raise Unify
           end
	| Tconstr(n1, ty_l1, _), Tconstr(n2, ty_l2, _) when same_types n1 n2 ->
           begin try
               List.iter2 unify ty_l1 ty_l2
             with
             | Invalid_argument _ -> raise Unify
           end
	| Tconstr(n1, ty_l1, abbrev1), Tconstr(n2, ty_l2, abbrev2) ->
           begin try
             let expected_ty = abbreviation n1 abbrev1 ty_l1 in
             unify expected_ty actual_ty
             with Not_found ->
               try let actual_ty = abbreviation n2 abbrev2 ty_l2 in
                   unify expected_ty actual_ty
               with Not_found -> raise Unify
           end	
	| Tarrow(k1, ty_arg1, ty_res1),
	  Tarrow(k2, ty_arg2, ty_res2) ->
	   if k1 = k2 then
	     begin unify ty_arg1 ty_arg2; unify ty_res1 ty_res2 end
	   else raise Unify
	| _ -> raise Unify
	       
let filter_product arity ty =
  let ty = typ_repr ty in
    match ty.t_desc with
      | Tproduct(l) ->
          if List.length l = arity then l else raise Unify
      | _ ->
          let ty_list = new_var_list arity in
          unify ty (product ty_list);
          ty_list

let filter_signal ty =
  let ty_arg = new_var () in
  unify ty (Initial.typ_signal ty_arg); ty_arg

let filter_arrow expected_k ty =
  let ty = typ_repr ty in
  match ty.t_desc with
  | Tarrow(actual_k, ty_arg, ty_res) ->
     actual_k, ty_arg, ty_res
  | _ ->
     let ty_arg = new_var () in
     let ty_res = new_var () in
     unify ty (arrowtype expected_k ty_arg ty_res);
     expected_k, ty_arg, ty_res

let filter_actual_arrow ty =
  let ty = typ_repr ty in
  match ty.t_desc with
  | Tarrow(actual_k, ty_arg, ty_res) ->
     actual_k, ty_arg, ty_res
  | _ -> assert false

(** All the function below are pure. They do not modify the internal *)
(** representation of types. This is mandatory for them to be used once *)
(** static typing is performed *)

(** Is-it a node ? *)
let is_a_node_name lname =
  let { info = { value_typ = { typ_body = typ_body } } } = 
    Modules.find_value lname in
  match typ_body.t_desc with
    | Tarrow(Tnode _, _, _) -> true | _ -> false

(** Is-it a function? *)
let is_a_function_name lname =
  let { info = { value_typ = { typ_body = ty } } } = 
    Modules.find_value lname in
  let ty = typ_repr ty in
  match ty.t_desc with
    | Tarrow(Tfun _, _, _) -> true | _ -> false

(* kind of a function type *)
let kind_of_arrowtype ty =
  let ty = typ_repr ty in
  match ty.t_desc with
  | Tarrow(k, _, _) -> k | _ -> assert false
							
let kind_of_node_name lname =
  let { info = { value_typ = { typ_body = ty } } } = 
    Modules.find_value lname in
  kind_of_arrowtype ty

(* Does a type scheme contains type variables *)
let nopolymorphism { typ_vars } = typ_vars = []
