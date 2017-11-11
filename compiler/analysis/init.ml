(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
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
open Global
       
(* typing errors *)
type error =
  | Iless_than of ty * ty (* not (expected_ty < actual_ty) *) 
  | Iless_than_i of t * t (* not (expected_i < actual_i) *) 
  | Iunify of ty * ty (* not (expected_ty = actual_ty) *) 
  | Iunify_i of t * t (* not (expected_i = actual_i) *) 
  | Ilast of Ident.t (* [last x] is un-initialized *)

exception Clash of error

let new_var () = 
  { i_desc = Ivar; i_index = symbol#name; i_level = !binding_level;
    i_inf = []; i_sup = []; i_visited = -1; 
    i_useful = false; i_polarity = Punknown }
let izero = 
  { i_desc = Izero; i_index = symbol#name; i_level = generic;
    i_inf = []; i_sup = [];
    i_visited = -1; i_useful = false; i_polarity = Punknown }
let ione = 
  { i_desc = Ione; i_index = symbol#name; i_level = generic;
    i_inf = []; i_sup = [];
    i_visited = -1; i_useful = false; i_polarity = Punknown   }
let funtype ty1 ty2 = Ifun(ty1, ty2)
let rec funtype_list ty_arg_list ty_res =
  match ty_arg_list with
  | [] -> ty_res
  | [ty] -> funtype ty ty_res
  | ty :: ty_arg_list -> funtype ty (funtype_list ty_arg_list ty_res)
let product l = Iproduct(l)
let atom i = Iatom(i)

(* basic operation on initialization values *)
let rec irepr i =
  match i.i_desc with
    | Ilink(i_son) ->
        let i_son = irepr i_son in
        i.i_desc <- Ilink(i_son);
        i_son
    | _ -> i

(* equality of two initialization tags *)
let equal i1 i2 =
  let i1 = irepr i1 in
  let i2 = irepr i2 in
  i1.i_index = i2.i_index
		 
let rec add i l =
  match l with
  | [] -> [i]
  | i1 :: l1 -> if equal i i1 then l else i1 :: (add i l1)

let rec remove i l =
  match l with
  | [] -> []
  | i1 :: l1 -> if equal i i1 then l1 else i1 :: (remove i l1)

let rec union l1 l2 = 
  let rec mem i l =
    match l with | [] -> false | i1 :: l -> (equal i i1) || (mem i l) in
  match l1, l2 with
  | [], l2 -> l2 | l1, [] -> l1
  | i :: l1, l2 -> if mem i l2 then union l1 l2 else i :: union l1 l2
							      
(** Sets the polarity of a type. *)
let polarity p i =
  match p, i.i_polarity with
    | _, Punknown -> i.i_polarity <- p
    | Punknown, polarity -> ()
    | _, polarity -> if p <> polarity then i.i_polarity <- Pplusminus

let increase_polarity p i =
  match p with
  | Punknown -> i.i_polarity <- p
  | _ -> if p <> i.i_polarity then i.i_polarity <- Pplusminus
      
(* saturate an initialization type. Every leaf must be initialized *)
let rec initialize is_zero ty =
  match ty with
  | Ifun(ty1, ty2) -> initialize is_zero ty1; initialize is_zero ty2
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
    | _ -> raise (Clash(Iunify_i(i, if is_zero then izero else ione)))

(** Sub-typing *)
let rec less left_ty right_ty =
  if left_ty == right_ty then ()
  else
    match left_ty, right_ty with
    | Ifun(ty1, ty2), Ifun(ty3, ty4) ->
       less ty2 ty4; less ty3 ty1
    | Iproduct(l1), Iproduct(l2) -> List.iter2 less l1 l2
    | Iatom(i1), Iatom(i2) -> iless i1 i2
    | _ -> raise (Clash(Iless_than(left_ty, right_ty)))

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
      | _ -> raise (Clash(Iless_than_i(left_i, right_i)))
		   
(** Unification *)
let rec unify left_ty right_ty =
  match left_ty, right_ty with
  | Ifun(ty1, ty2), Ifun(ty3, ty4) -> unify ty1 ty3; unify ty2 ty4
  | Iproduct(ty_list1), Iproduct(ty_list2) ->
     List.iter2 unify ty_list1 ty_list2
  | Iatom(left_i), Iatom(right_i) ->
     iunify left_i right_i
  | _ -> raise (Clash(Iunify(left_ty, right_ty)))

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
         increase_polarity right_i.i_polarity left_i
      | Ivar, Izero -> iinitialize true left_i
      | Ivar, Ione -> iinitialize false left_i
      | Izero, Ivar -> iinitialize true right_i
      | Ione, Ivar -> iinitialize false right_i
      | (Izero, Izero) | (Ione, Ione) -> ()
      | _ -> raise (Clash(Iunify_i(left_i, right_i)))
		   
(** Computing an initialization type from a type *)
let rec skeleton ty =
  match ty.t_desc with
  | Tvar -> atom (new_var ())
  | Tfun(_, _, ty1, ty2) -> funtype (skeleton ty1) (skeleton ty2)
  | Tproduct(ty_list) -> product (List.map skeleton ty_list)
  | Tconstr(_, _, _) | Tvec _ -> atom (new_var ())
  | Tlink(ty) -> skeleton ty
			  
let rec skeleton_on_i i ty =
  match ty.t_desc with
  | Tvar -> atom i
  | Tfun(_, _, ty1, ty2) ->
     funtype (skeleton_on_i i ty1) (skeleton_on_i i ty2)
  | Tproduct(ty_list) -> product (List.map (skeleton_on_i i) ty_list)
  | Tconstr(_, _, _) | Tvec _ -> atom i
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
  | Ifun(ty1, ty2) -> mark useful right ty2; mark useful (not right) ty1
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
(*
let rec shorten ty =
  match ty with
  | Ifun(ty1, ty2) -> shorten ty1; shorten ty2
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
        *)

(* Remove cycles *)
(* For every type t, we recursively compute the set of t_inf s.t. t_inf < t *)
(* and t < t_sup. If t belongs to t_inf, all types in relation are equal *)
(* and unified. The same applies for t_sup. *)
let rec shorten ty =
  match ty with
  | Ifun(ty1, ty2) -> shorten ty1; shorten ty2
  | Iproduct(ty_list) -> List.iter shorten ty_list
  | Iatom(i) -> ishorten i

and ishorten i =
  let i = irepr i in
  match i.i_desc with
  | Izero | Ione -> ()
  | Ilink(i) -> ishorten i
  | Ivar ->
     i.i_visited <- 0;
     (* only keep a dependence a+ < b- *)
     let inf = remove_polarities false (short_list true [i] [] i.i_inf) in
     let sup = remove_polarities true (short_list false [i] [] i.i_sup) in
     i.i_inf <- inf;
     i.i_sup <- sup;
     i.i_visited <- 1       
		      
and short_list is_right stack acc i_list =
  List.fold_left (short is_right stack) acc i_list

(* only keep a dependence a+ < b- *)
and remove_polarities right i_list =
  let clear right acc i_right =
    match i_right.i_polarity with
    | Pminus when right -> acc
    | Pplus when not right -> acc
    | _ -> i_right :: acc in
  List.fold_left (clear right) [] i_list
    
and short is_right stack acc i =
  match i.i_desc with
  | Izero | Ione -> acc
  | Ilink(i) -> short is_right stack acc i
  | Ivar ->
    match i.i_visited with
    | -1 -> (* never visited *)
      i.i_visited <- 0;
      let acc =
        if i.i_useful then add i acc
        else
          short_list
            is_right (i :: stack) acc (if is_right then i.i_sup else i.i_inf) in
      i.i_visited <- -1;
      acc
    | 0 -> (* currently visited *)
      iunify_stack stack i; 
      acc
    | _ -> (* visited in a previous pass *) 
      (* the variable is added only if it is useful *)
      if i.i_useful then add i acc else union i.i_inf acc  

let rec shorten ty =
  match ty with
  | Ifun(ty1, ty2) -> shorten ty1; shorten ty2
  | Iproduct(ty_list) -> List.iter shorten ty_list
  | Iatom(i) -> ishorten i

and ishorten i =
  let i = irepr i in
  match i.i_desc with
  | Izero | Ione -> ()
  | Ilink(i) -> ishorten i
  | Ivar ->
     i.i_visited <- 0;
     (* only keep a dependence a+ < b- *)
     let inf = remove_polarities false (short_list true [i] [] i.i_inf) in
     let sup = remove_polarities true (short_list false [i] [] i.i_sup) in
     i.i_inf <- inf;
     i.i_sup <- sup;
     i.i_visited <- 1       
		      
and short_list is_right stack acc i_list =
  List.fold_left (short is_right stack) acc i_list

(* only keep a dependence a+ < b- *)
and remove_polarities right i_list =
  let clear right acc i_right =
    match i_right.i_polarity with
    | Pminus when right -> acc
    | Pplus when not right -> acc
    | _ -> i_right :: acc in
  List.fold_left (clear right) [] i_list
    
and short is_right stack acc i =
  match i.i_desc with
  | Izero | Ione -> acc
  | Ilink(i) -> short is_right stack acc i
  | Ivar ->
    match i.i_visited with
    | -1 -> (* never visited *)
      i.i_visited <- 0;
      let acc =
        if i.i_useful then add i acc
        else
          short_list
            is_right (i :: stack) acc (if is_right then i.i_sup else i.i_inf) in
      i.i_visited <- -1;
      acc
    | 0 -> (* currently visited *)
      iunify_stack stack i; 
      acc
    | _ -> (* visited in a previous pass *) 
      (* the variable is added only if it is useful *)
      if i.i_useful then add i acc else union i.i_inf acc  

(* Simplification of a type *)
(*- only keep a relation a- < b+; remove a+ < b *)
(*- a variable a+ which has no inf. can be replaced by 0;
 *- if it has a single sup. b, it can be replaced by it
 *- if it has a single inf. b, it can be replaced by it;
 *- a variable a- which has no sup. can be replaced by 1 *)

let rec simplify right ty =
  match ty with
  | Ifun(ty1, ty2) -> funtype (simplify (not right) ty1) (simplify right ty2)
  | Iproduct(ty_list) -> product(List.map (simplify right) ty_list)
  | Iatom(i) -> Iatom(isimplify right i)

and isimplify right i =
  let i = irepr i in
  match i.i_desc with
  | Izero | Ione  | Ilink _ -> i
  | Ivar ->
    if right then
      match i.i_inf with
      | [] when i.i_polarity = Pplus -> izero
      | [i_inf] ->
        increase_polarity Pplus i_inf;
        i_inf.i_sup <- union (remove i i_inf.i_sup) i.i_sup; i_inf
      | _ -> i
    else
      match i.i_sup with
      | [] when i.i_polarity = Pminus -> ione
      | [i_sup] -> increase_polarity Pminus i_sup;
        i_sup.i_inf <- union (remove i i_sup.i_inf) i.i_inf;
        i_sup
      | _ -> i
      
(** Generalisation of a type *)
(* the level of generalised type variables *)
(* is set to [generic]. Returns [generic] when a sub-term *)
(* can be generalised *)
	      
let list_of_vars = ref []
		       
let rec gen ty =
  match ty with
  | Ifun(ty1, ty2) -> gen ty1; gen ty2
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
let generalise ty =
  list_of_vars := [];
  (* we mark useful variables *)
  mark true true ty;
  shorten ty;
  let ty = simplify true ty in
  gen ty;
  let rel = Pinit.relation !list_of_vars in
  ignore rel;
  { typ_vars = !list_of_vars; typ = ty }

(** Instantiation of a type *)
(* save and cleanup links *)
let links = ref []
    
let save link = links := link :: !links
let cleanup () = List.iter (fun i -> i.i_desc <- Ivar) !links; links := []
									  
let rec copy ti ty =
  let { t_desc = t_desc } as ty = Types.typ_repr ty in
  match ti, t_desc with
  | Ifun(ti1, ti2), Tfun(_, _, ty1, ty2) ->
     funtype (copy ti1 ty1) (copy ti2 ty2)
  | Iproduct(ti_list), Tproduct(ty_list) ->
     begin try product (List.map2 copy ti_list ty_list)
	   with | _ -> assert false end
  | Iatom(i), _ -> skeleton_on_i (icopy i) ty
  | _ -> assert false

and icopy i =
  match i.i_desc with
  | Ivar ->
     if i.i_level = generic
     then
       let sup_list = List.map icopy i.i_sup in
       let v = { (new_var ()) with i_sup = sup_list } in
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
let instance { typ_vars = ti_list; typ = ti } ty =
  let ti = copy ti ty in
  cleanup ();
  ti

(* type instance *)
let instance { value_init = tis_opt } ty =
  (* build a default signature *)
  let default ty =
    let i = new_var () in
    skeleton_on_i i ty in
  let ti = match tis_opt with
    | None -> 
       (* if no initialization signature is declared, a default one is built *)
       (* from the type signature *)
       default ty
    | Some(tis) -> instance tis ty in
  ti

let filter_arrow ty =
  match ty with
  | Ifun(ty1, ty2) -> ty1, ty2
  | _ -> assert false
