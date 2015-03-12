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
(* initialization types and basic operations over these types *)

open Misc
open Deftypes
open Definit

(** Sets the polarity of a type. *)
let polarity p i =
  match p, i.i_polarity with
    | _, Punknown -> i.i_polarity <- p
    | Punknown, polarity -> ()
    | _, polarity -> if p <> polarity then i.i_polarity <- Pplusminus

(* typing errors *)
exception Unify

let new_var () = 
  { i_desc = Ivar; i_index = symbol#name; i_level = !binding_level;
    i_inf = []; i_sup = []; i_visited = -1; 
    i_useful = true; i_polarity = Punknown }
let izero = 
  { i_desc = Izero; i_index = symbol#name; i_level = generic;
    i_inf = []; i_sup = [];
    i_visited = -1; i_useful = true; i_polarity = Punknown }
let ione = 
  { i_desc = Ione; i_index = symbol#name; i_level = generic;
    i_inf = []; i_sup = [];
    i_visited = -1; i_useful = true; i_polarity = Punknown   }
let product l = Iproduct(l)
let atom i = Iatom(i)

let add i l = if List.memq i l then l else i :: l

let rec union l1 l2 = 
  match l1, l2 with
    [], l2 -> l2
  | l1, [] -> l1
  | x :: l1, l2 ->
      if List.memq x l2 then union l1 l2 else x :: union l1 l2

(* basic operation on initialization values *)
let rec irepr i =
  match i.i_desc with
    | Ilink(i_son) ->
        let i_son = irepr i_son in
        i.i_desc <- Ilink(i_son);
        i_son
    | _ -> i

(* saturate an initialization type. Every leaf must be initialized *)
let rec initialize is_zero ty =
  match ty with
    | Iproduct(ty_list) -> List.iter (initialize is_zero) ty_list
    | Iatom(i) -> iinitialize is_zero i

and iinitialize is_zero i =
  let i = irepr i in
  match i.i_desc with
    | Izero when is_zero -> ()
    | Ione when not is_zero -> ()
    | Ivar -> 
        i.i_desc <- Ilink(if is_zero then izero else ione); 
        List.iter (iinitialize is_zero) (if is_zero then i.i_inf else i.i_sup)
    | Ilink(i) -> iinitialize is_zero i
    | _ -> raise Unify

(** Sub-typing *)
let rec less left_ty right_ty =
  if left_ty == right_ty then ()
  else
    match left_ty, right_ty with
      | Iproduct(l1), Iproduct(l2) -> List.iter2 less l1 l2
      | Iatom(i1), Iatom(i2) -> iless i1 i2
      | _ -> raise Unify

and iless left_i right_i =
  if left_i == right_i then ()
  else
    let left_i = irepr left_i in
    let right_i = irepr right_i in
    if left_i == right_i then ()
    else
      match left_i.i_desc, right_i.i_desc with
        | (Izero, _) | (_, Ione) -> ()
        | _, Izero -> iinitialize true left_i
        | Ione, _ -> iinitialize false right_i
        | Ivar, Ivar ->
            (* i1,...,in < i < j1,...,jk  with  *)
            (* l1,...,lm < r < s1,...,sr *)
            right_i.i_inf <- add left_i right_i.i_inf;
            left_i.i_sup <- add right_i left_i.i_sup
        | _ -> raise Unify

(** Unification *)
let rec unify left_ty right_ty =
  match left_ty, right_ty with
    | Iproduct(ty_list1), Iproduct(ty_list2) ->
        List.iter2 (fun ty1 ty2 -> unify ty1 ty2) ty_list1 ty_list2
    | Iatom(left_i), Iatom(right_i) ->
        iunify left_i right_i
    | _ -> raise Unify

and iunify left_i right_i =
  if left_i == right_i then ()
  else
    let left_i = irepr left_i in
    let right_i = irepr right_i in
    if left_i == right_i then ()
    else
      match left_i.i_desc, right_i.i_desc with
        | Ivar, Ivar ->
            (* i1,...,in < i < j1,...,jk  with  *)
            (* l1,...,lm < r < s1,...,sr *)
            right_i.i_inf <- union left_i.i_inf right_i.i_inf;
            right_i.i_sup <- union left_i.i_sup right_i.i_sup;
            (* sets the level *)
            if right_i.i_level > left_i.i_level 
            then right_i.i_level <- left_i.i_level;
            right_i.i_desc <- Ilink(left_i);
            (* sets the polarity *)
            polarity left_i.i_polarity right_i;
            polarity right_i.i_polarity left_i
        | Ivar, Izero -> iinitialize true left_i
        | Ivar, Ione -> iinitialize false left_i
        | Izero, Ivar -> iinitialize true right_i
        | Ione, Ivar -> iinitialize false right_i
        | (Izero, Izero) | (Ione, Ione) -> ()
        | _ -> raise Unify

(** Computing an initialization type from a type *)
let rec skeleton ty =
  match ty.t_desc with
    | Tvar -> atom (new_var ())
    | Tproduct(ty_list) -> product (List.map skeleton ty_list)
    | Tconstr(_, ty_list, _) -> atom (new_var ())
    | Tlink(ty) -> skeleton ty

let rec skeleton_on_i i ty =
  match ty.t_desc with
    | Tvar -> atom i
    | Tproduct(ty_list) -> product (List.map (skeleton_on_i i) ty_list)
    | Tconstr(_, ty_list, _) -> atom i
    | Tlink(ty) -> skeleton_on_i i ty

let rec iunify_stack stack i =
  match stack with
    | [] -> ()
    | i_stack :: stack ->
        if i_stack == i then ()
        else
          let i_stack = irepr i_stack in
          let i = irepr i in
            if i_stack == i then ()
            else
              begin iunify i_stack i; iunify_stack stack i end
                
(** Mark useful/useless types and sets the polarity *)
(* reduces dependences by eliminating intermediate variables *)
(* we first mark useful variables (variables which appear in *)
(* the final type. We also compute polarities *)
let rec mark useful right ty =
  match ty with
    | Iproduct(ty_list) -> List.iter (mark useful right) ty_list
    | Iatom(i) -> imark useful right i

and imark useful right i =
  let i = irepr i in
  match i.i_desc with
    | Ivar ->
        i.i_useful <- useful;
        if useful then
          match i.i_polarity, right with
            | Punknown, true -> i.i_polarity <- Pplus
            | Punknown, false -> i.i_polarity <- Pminus
            | (Pminus, true) | Pplus, false -> i.i_polarity <- Pplusminus
            | _ -> ()
        else i.i_polarity <- Punknown
    | Izero | Ione | Ilink _ -> ()

(** Shorten/simplification an initialization type.*)
(* For every type t, we recursively compute the set of t_inf s.t. t_inf < t *)
(* and t < t_sup. If t belongs to t_inf, all types in relation are equal *)
(* and unified. The same applies for t_sup. *)
(* Two simplifications are made: *)
(* - every useless (intermediate) variable is eliminated *)
(* - a useful variable which can be generalized and has negative polarity a- *)
(*   can be unified with 1. *)
(* - a useful variable which can be generalized and has positive polarity a+ *)
(*   can be unified with 0. *)
let rec shorten ty =
  match ty with
    | Iproduct(ty_list) -> List.iter shorten ty_list
    | Iatom(i) -> ishorten i

and ishorten i =
  let i = irepr i in
  match i.i_desc with
    | Izero | Ione -> ()
    | Ilink(i) -> ishorten i
    | Ivar ->
        i.i_visited <- 0;
        i.i_inf <- short_infs [i] [] i.i_inf;
        i.i_sup <- short_sups [i] [] i.i_sup;
        i.i_visited <- 1

and short_infs stack acc i_list =
  List.fold_left (short_inf stack) acc i_list

and short_sups stack acc i_list =
  List.fold_left (short_sup stack) acc i_list

and short_inf stack acc i =
  match i.i_desc with
    | Izero | Ione -> acc
    | Ilink(i) -> short_inf stack acc i
    | Ivar when (i.i_polarity = Pplus) && (i.i_level > !binding_level) ->
        iinitialize true i; acc
    | Ivar when (i.i_polarity = Pminus) && (i.i_level > !binding_level) ->
        iinitialize false i; acc
    | Ivar ->
        match i.i_visited with
          | -1 -> (* never visited *)
              i.i_visited <- 0;
              short_infs (i :: stack) acc i.i_inf
          | 0 -> (* currently visited *)
              iunify_stack stack i; 
              (* the variable is added only if it is useful *)
              if i.i_useful then add i acc else acc
          | _ -> (* visited in a previous pass *) 
              union i.i_inf acc

and short_sup stack acc i =
  match i.i_desc with
    | Izero | Ione -> acc
    | Ilink(i) -> short_sup stack acc i
    | Ivar when (i.i_polarity = Pplus) && (i.i_level > !binding_level) ->
        iinitialize true i; acc
    | Ivar when (i.i_polarity = Pminus) && (i.i_level > !binding_level) ->
        iinitialize false i; acc
    | Ivar ->
        match i.i_visited with
          | -1 -> (* never visited and *)
              i.i_visited <- 0;
              short_sups (i :: stack) acc i.i_sup
          | 0 -> (* currently visited *)
              iunify_stack stack i; 
              (* the variable is added only if it is useful *)
              if i.i_useful then add i acc else acc
          | _ -> (* visited in a previous pass *) 
              union i.i_sup acc

(** Generalisation of a type *)
(* the level of generalised type variables *)
(* is set to [generic]. Returns [generic] when a sub-term *)
(* can be generalised *)

let list_of_vars = ref []

let rec gen ty =
  match ty with
    | Iproduct(ty_list) -> List.iter gen ty_list
    | Iatom(i) -> ignore (igen i)

and igen i =
  let i = irepr i in
    match i.i_desc with
    | Izero | Ione -> i.i_level
    | Ivar ->
        if i.i_level > !binding_level
        then 
          begin
            i.i_level <- generic;
            let level1 = gen_set i.i_inf in
            let level2 = gen_set i.i_sup in
            let level = min level1 level2 in
            i.i_level <- level;
            if level = generic then list_of_vars := i :: !list_of_vars
          end;
        i.i_level
    | Ilink(link) -> igen link

and gen_set l = List.fold_left (fun acc i -> max (igen i) acc) generic l

(** Main generalisation function *)
let generalise ty_arg_list ty_res =
  list_of_vars := [];
  (* we mark useful variables *)
  List.iter (mark true false) ty_arg_list;
  mark true true ty_res;
  List.iter shorten ty_arg_list;
  shorten ty_res;
  List.iter (fun ty -> ignore (gen ty)) ty_arg_list;
  ignore (gen ty_res);
  { typ_vars = !list_of_vars; typ_args = ty_arg_list; typ_res = ty_res }

(** Instantiation of a type *)
(* save and cleanup links *)
let links = ref []
    
let save link = links := link :: !links
let cleanup () = List.iter (fun i -> i.i_desc <- Ivar) !links; links := []

let rec copy ty =
  match ty with
    | Iproduct(ty_list) -> product (List.map copy ty_list)
    | Iatom(i) -> atom (icopy i)

and icopy i =
  match i.i_desc with
    | Ivar ->
        if i.i_level = generic
        then
          let v = new_var () in
          i.i_desc <- Ilink(v);
          save i;
          v
        else i
    | Ilink(link) ->
        if i.i_level = generic then link else icopy link
    | Izero ->
        if i.i_level = generic then izero else i
    | Ione ->
        if i.i_level = generic then ione else i
        
(* instanciation *)
let instance { typ_vars = ty_list; typ_args = ty_arg_list; typ_res = ty_res } =
  let ty_arg_list = List.map copy ty_arg_list in
  let ty_res = copy ty_res in
  cleanup ();
  ty_arg_list, ty_res
  

module Printer = struct
  open Format
  open Pp_tools

  (* type variables are printed 'a, 'b,... *)
  let type_name = new name_assoc_table int_to_alpha

  let name ff index = fprintf ff "%s" (type_name#name index)

  let rec init ff i = match i.i_desc with
    | Izero -> fprintf ff "0"
    | Ione -> fprintf ff "1"
    | Ilink(i) -> init ff i
    | Ivar -> name ff i.i_index

  let rec typ ff = function
    | Iatom(i) -> init ff i
    | Iproduct(ty_list) ->
        fprintf ff "@[%a@]" (print_list_r typ "("" *"")") ty_list

  let signature ff
      { typ_vars = ty_list; typ_args = ty_arg_list; typ_res = ty_res } = 
    let arg_list ff = function
      | [] -> fprintf ff "1"
      | ty_arg_list -> 
          fprintf ff "@[%a@]" (print_list_r typ """ *""") ty_arg_list in
    fprintf ff "@[%a -> %a@]" arg_list ty_arg_list
      typ ty_res
end

