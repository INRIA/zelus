(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* types.ml : basic operations over types *)

open Misc
open Ident
open Lident
open Deftypes
open Global
open Modules
open Zelus

(* making types *)
let make ty =
  { t_desc = ty; t_level = generic; t_index = symbol#name }
let product ty_list =
  make (Tproduct(ty_list))

let constr name ty_list abbrev =
  make (Tconstr(name, ty_list, abbrev))
let nconstr name ty_list = constr name ty_list (ref Tnil)

let new_discrete_var () =
  { t_desc = Tvar; t_level = !binding_level; t_index = symbol#name }
let new_var () =
  { t_desc = Tvar; t_level = !binding_level; t_index = symbol#name }
let new_generic_var () =
  { t_desc = Tvar; t_level = generic; t_index = symbol#name }
let rec new_var_list n =
  match n with
    0 -> []
  | n -> (new_var ()) :: new_var_list (n - 1)
let forall l typ_body = { typ_vars = l; typ_body = typ_body }

(* typing errors *)
exception Unify


(* comparing statefull and stateless expressions. A stateless one *)
(* is allowed in a context where a statefull one is expected *)
let less_than actual_k expected_k =
  match actual_k, expected_k with
    | (Tany, _) | (Tcont, Tcont) -> ()
    | (Tdiscrete(s1), Tdiscrete(s2)) -> if not (s1 <= s2) then raise Unify
    | _ -> raise Unify

(** The type of zero-crossing condition. [zero] when under a continuous *)
(** context. [bool] otherwise. *)
let zero_type expected_k =
  match expected_k with
    | Tany | Tdiscrete _ -> Initial.typ_bool 
    | Tcont -> Initial.typ_zero

(* The kind on the right of a [scpat on e] signal pattern. *)
(* When [expected_k = Tcont] or [expected_k = Tany] *)
(* then [e] can be of kind [Tdiscrete(false)]. As [e] is aligned *)
(* with either a zero-crossing or combinatorial function, it cannot introduce *)
(* a discontinuity *)
let on_type expected_k =
  match expected_k with
    | Tcont | Tany -> Tdiscrete(false)
    | _ -> expected_k

let is_combinatorial expected_k = 
  match expected_k with | Tany -> true | Tcont | Tdiscrete _ -> false

let is_discrete expected_k =
  match expected_k with | Tdiscrete(true) -> true | _ -> false

let is_continuous expected_k =
  match expected_k with
    | Tany | Tdiscrete _ -> false | Tcont -> true

let is_statefull expected_k =
  match expected_k with
    | Tdiscrete(true) | Tcont -> true | _ -> false

(** Make a discrete sort. In case [expected_k = Tany], return [Tany] *)
let lift_to_discrete expected_k =
  match expected_k with
    | Tcont | Tdiscrete(true) -> Tdiscrete(true)
    | Tany | Tdiscrete _ -> expected_k

(** Make a stateless from an expected kind *)
let any = 
  function | Tany -> Tany | Tcont -> Tany | Tdiscrete _ -> Tdiscrete(false)

(* shortening types *)
let rec typ_repr ty =
  match ty.t_desc with
    | Tlink(ty_son) ->
        let ty_son = typ_repr ty_son in
          ty.t_desc <- Tlink(ty_son);
          ty_son
    | _ -> ty

(* occur check and level modification *)
let rec occur_check level index ty =
  let rec check ty =
    match ty.t_desc with
      | Tvar ->
          if ty == index
          then raise Unify
          else if ty.t_level > level then ty.t_level <- level
      | Tproduct(ty_list) -> List.iter check ty_list
      | Tconstr(name, ty_list, _) ->
           List.iter check ty_list
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
    begin match ty.t_desc with
        Tvar ->
          if ty.t_level > !binding_level
          then if is_gen
          then (ty.t_level <- generic;
                list_of_typ_vars := ty :: !list_of_typ_vars)
            else ty.t_level <- !binding_level
      | Tproduct(ty_list) ->
          ty.t_level <-
            List.fold_left (fun level ty -> min level (gen_ty is_gen ty))
            notgeneric ty_list
      | Tconstr(name, ty_list,_) ->
          ty.t_level <- List.fold_left
            (fun level ty -> min level (gen_ty is_gen ty))
            notgeneric ty_list
      | Tlink(link) ->
          ty.t_level <- gen_ty is_gen link
    end;
    ty.t_level

(* main generalisation function *)
let gen non_expensive typ_body =
  list_of_typ_vars := [];
  begin match typ_body with
    | Tvalue(ty) ->
        ignore (gen_ty non_expensive ty)
    | Tsignature(_, _, ty_arg_list, ty_res) ->
        ignore (List.map (gen_ty non_expensive) ty_arg_list);
        ignore (gen_ty non_expensive ty_res)
  end;
  { typ_vars = !list_of_typ_vars; typ_body = typ_body }

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

(* instanciation *)
let instance_of_type { typ_body = typ_body } =
  let typ_body =
    match typ_body with
      | Tvalue(ty) -> copy ty
      | Tsignature _ -> raise Unify in
  cleanup ();
  typ_body

let instance_of_type_signature { typ_vars = typ_vars; typ_body = typ_body } =
  let typ_body =
    match typ_body with
      | Tvalue _ -> raise Unify
      | Tsignature(k, is_safe, ty_arg_list, ty_res) ->
          k, is_safe, List.map copy ty_arg_list, copy ty_res in
  let _ = List.map typ_repr typ_vars in
  cleanup ();
  typ_body

let constr_instance { constr_res = ty_res } =
  let ty_res = copy ty_res in
    cleanup ();
    { constr_res = ty_res }

let label_instance { label_arg = ty_arg; label_res = ty_res } =
  let ty_arg = copy ty_arg in
  let ty_res = copy ty_res in
    cleanup ();
    { label_arg = ty_arg; label_res = ty_res }


let subst ty_var ty =
  match ty_var.t_desc with
      Tvar -> ty_var.t_desc <- Tlink(ty)
    | _ -> assert false

let abbreviation q abbrev ty_list =
    let { info = ty_desc } = find_type (Modname q) in
  let find q =
      match ty_desc.type_desc with
          Abbrev(ty_list, ty) -> ty_list, ty
        | _ -> raise Not_found in
    try
      let arg_list, ty =
        match !abbrev with
            Tnil ->
              let (arg_list, ty) = find q in
                abbrev := Tcons(arg_list, ty);
                (arg_list, ty)
          | Tcons(arg_list, ty) -> arg_list, ty in

      let new_arg_list = List.map copy arg_list in
      let new_ty = copy ty in
        cleanup ();
        List.iter2 subst new_arg_list ty_list;
        new_ty
    with
        Not_found -> raise Unify


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
      | Tconstr(n1, ty_l1, abbrev), _ ->
          let expected_ty = abbreviation n1 abbrev ty_l1 in
            unify expected_ty actual_ty
      | _, Tconstr(n2, ty_l2, abbrev) ->
          let actual_ty = abbreviation n2 abbrev ty_l2 in
            unify expected_ty actual_ty
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

(** All the function below are pure. They do not modify the internal *)
(** representation of types. This is mandatory for them to be used once *)
(** static typing is performed *)

    
(** A function which returns either the type argument of a signal *)
(** or nothing. *)
let rec is_a_signal { t_desc = desc } =
  match desc with
    | Tconstr(id, [ty], _) when id = Initial.sig_ident -> Some(ty)
    | Tlink(link) -> is_a_signal link
    | _ -> None

(** Is-it a node ? *)
let is_a_node lname =
  let { info = { value_typ = { typ_body = typ_body } } } = 
    Modules.find_value lname in
  match typ_body with
    | Tsignature((Tdiscrete(true) | Tcont), _, _, _) -> true | _ -> false

(** Is-it a safe function ? *)
let is_a_safe_function lname =
  let { info = { value_typ = { typ_body = typ_body } } } = 
    Modules.find_value lname in
  match typ_body with
    | Tsignature(Tany, is_safe, _, _) -> is_safe | _ -> false

(** Is-it a function ? *)
let is_a_function lname =
  let { info = { value_typ = { typ_body = typ_body } } } = 
    Modules.find_value lname in
  match typ_body with
    | Tsignature(Tany, _, _, _) -> true | _ -> false

(** Is-it a safe function ? *)
let is_a_hybrid_node lname =
  let { info = { value_typ = { typ_body = typ_body } } } = 
    Modules.find_value lname in
  match typ_body with
    | Tsignature(Tcont, _, _, _) -> true | _ -> false

let kind_of_node lname =
  let { info = { value_typ = { typ_body = typ_body } } } = 
    Modules.find_value lname in
  match typ_body with
    | Tsignature(k, _, _, _) -> k | _ -> Tany



