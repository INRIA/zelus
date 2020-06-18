(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
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

(* making types *)
let make ty =
  { t_desc = ty; t_level = generic; t_index = symbol#name }
let product ty_list =
  make (Tproduct(ty_list))
let vec ty e = make (Tvec(ty, e))
let funtype k n_opt ty_arg ty_res =
  make (Tfun(k, n_opt, ty_arg, ty_res))
let rec funtype_list k ty_arg_list ty_res =
  match ty_arg_list with
  | [] -> ty_res
  | [n_opt, ty] -> funtype k n_opt ty ty_res
  | (n_opt, ty) :: ty_arg_list ->
     funtype (Tstatic(true)) n_opt ty (funtype_list k ty_arg_list ty_res)

(** Make size expressions. Apply simple simplification rules *)
let plus si1 si2 =
  match si1, si2 with
    | Tconst(0), _ -> si2
    | _, Tconst(0) -> si1
    | Top(Tminus, si1, Tconst(1)), Tconst(1) ->
      (* (si1 - 1) + 1 = si1 *) si1
    | _ -> Top(Tplus, si1, si2)
let minus si1 si2 =
  match si1, si2 with
    | _, Tconst(0) -> si1
    | _ -> Top(Tminus, si1, si2)
let const i = Tconst i
let global ln = Tglobal(ln)
let name n = Tname(n)
                  
let constr name ty_list abbrev = make (Tconstr(name, ty_list, abbrev))
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

(** Set of free size variables in a type *)
let rec fv acc { t_desc = desc } =
  match desc with
  | Tvar -> acc
  | Tproduct(ty_list) | Tconstr(_, ty_list, _) -> List.fold_left fv acc ty_list
  | Tvec(ty_arg, size) -> fv (fv_size acc size) ty_arg
  | Tfun(_, _, ty_arg, ty_res) -> fv (fv acc ty_arg) ty_res
  | Tlink(ty_link) -> fv acc ty_link

and fv_size acc si =
  match si with
  | Tconst _ | Tglobal _ -> acc
  | Tname(n) -> S.add n acc
  | Top(_, si1, si2) -> fv_size (fv_size acc si1) si2
  
(* replace size variables in [ty] by their value in the environment [senv] *)
let rec subst_in_type senv ({ t_desc = desc; t_index = index } as ty) =
  match desc with
  | Tvar -> ty
  | Tproduct(ty_list) -> product (List.map (subst_in_type senv) ty_list)
  | Tconstr(gl, ty_list, abbrev) ->
     constr gl (List.map (subst_in_type senv) ty_list) abbrev
  | Tvec(ty_arg, si) ->
     vec (subst_in_type senv ty_arg) (subst_in_size senv si)
  | Tlink(ty_link) -> subst_in_type  senv ty_link
  | Tfun(k, n_opt, ty_arg, ty_res) ->
     let ty_arg = subst_in_type senv ty_arg in
     let n_opt, ty_res =
       match n_opt with
       | None -> n_opt, subst_in_type senv ty_res
       | Some(n) ->
	  let m = Ident.fresh (Ident.source n) in
	  Some(m), subst_in_type (Env.add n (Tname(m)) senv) ty_res in
     funtype k n_opt ty_arg ty_res

and subst_in_size senv si =
  match si with
  | Tconst _ | Tglobal _ -> si
  | Top(op, si1, si2) ->
     Top(op, subst_in_size senv si1, subst_in_size senv si2)
  | Tname(n) ->
     try Env.find n senv with | Not_found -> Tname(n)
  
(** Remove dependences from a type *)
(* [t1 -A-> t2] becomes [t1 -> t2];
 - [t1 -D-> t2] becomes [(t1, t2) node];
 - [t1 -C-> t2] becomes [(t1, t2) hybrid];
 - [(n: t1) -k-> t2] is treated as [t1 -k-> t2]
 - [t[si]] becomes [t] *)
let rec remove_dependences ({ t_desc = desc } as ty) =
  let typ_node ty_arg ty_res =
    Initial.constr { qual = current_module (); id = "node" } [ty_arg; ty_res] in
  let typ_hybrid ty_arg ty_res =
    Initial.constr { qual = current_module (); id = "hybrid" }
		   [ty_arg; ty_res] in
  let typ_proba ty_arg ty_res =
    Initial.constr { qual = current_module (); id = "proba" }
		   [ty_arg; ty_res] in
  let abbrev = function
    | Tnil -> Tnil
    | Tcons(ty_list, ty) ->
       Tcons(List.map remove_dependences ty_list, remove_dependences ty) in
  match desc with
  | Tvar -> ty
  | Tproduct(ty_list) -> product(List.map remove_dependences ty_list)
  | Tconstr(gl, ty_list, a) ->
     constr gl (List.map remove_dependences ty_list) (ref (abbrev !a))
  | Tvec(ty_arg, _) -> Initial.typ_array (remove_dependences ty_arg)
  | Tlink(ty_link) -> remove_dependences ty_link
  | Tfun(k, _, ty_arg, ty_res) ->
     let ty_arg = remove_dependences ty_arg in
     let ty_res = remove_dependences ty_res in
     match k with
     | Tany | Tstatic _ | Tdiscrete false ->
			   funtype Tany None ty_arg ty_res
     | Tdiscrete true -> typ_node ty_arg ty_res
     | Tcont -> typ_hybrid ty_arg ty_res
     | Tproba -> typ_proba ty_arg ty_res
			    
(* typing errors *)
exception Unify

(* comparing statefull and stateless expressions. A stateless one *)
(* is allowed in a context where a statefull one is expected *)
let less_than actual_k expected_k =
  match actual_k, expected_k with
  | (Tstatic(true), _)
  | (Tany, (Tany | Tdiscrete _ | Tcont | Tproba))
  | (Tcont, Tcont) -> ()
  | (Tdiscrete(s1), Tdiscrete(s2)) -> if not (s1 <= s2) then raise Unify
  | (Tdiscrete _, Tproba) | (Tproba, Tproba) -> ()
  | _ -> raise Unify

(* If a function with type t1 -k2-> t2 is used in a context with kind k1 *)
(* then, its argument must be of kind k1 ^ k2 *)
let lift k1 k2 =
  match k1, k2 with
  | _, Tstatic(false) -> k1
  | _, Tstatic(true) -> Tstatic(true)
  | _ -> less_than k2 k1; k1

(* function types introduced in a context [k] must be combinatorial *)
let intro = function
  | (Tstatic _ | Tany) as k -> k | Tdiscrete _ | Tcont | Tproba -> Tany

let run_type expected_k =
  let ty_arg = new_var () in
  let ty_res = new_var () in
  funtype expected_k None ty_arg ty_res

							      
(* Check that a type has itself kind k. *)
(***** removed the constraint: it forbids function unless k = S *)
let rec kind k { t_desc = desc } =
  match desc with
  | Tvar -> ()
  | Tproduct(ty_list) | Tconstr(_, ty_list, _) -> List.iter (kind k) ty_list
  | Tvec(ty_arg, _) -> kind k ty_arg
  | Tlink(ty_link) -> kind k ty_link
  | Tfun _ -> ()
(***** when (k = Tstatic(true)) -> () | _ -> raise Unify *)

let fully_applied ty = try kind Tany ty; true with Unify -> false
				   
(** The type of zero-crossing condition. [zero] when under a continuous *)
(** context. [bool] otherwise. *)
let zero_type expected_k =
  match expected_k with
    | Tstatic _ | Tany | Tdiscrete _ | Tproba -> Initial.typ_bool 
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

let is_combinatorial_kind expected_k = 
  match expected_k with
  | Tany -> true | Tstatic _ | Tcont | Tdiscrete _ | Tproba -> false

let is_discrete_kind expected_k =
  match expected_k with
  | Tdiscrete(true) | Tproba -> true
  | Tcont | Tdiscrete(false) | Tany | Tstatic _ -> false

let is_continuous_kind expected_k =
  match expected_k with
    | Tstatic _ | Tany | Tdiscrete _ | Tproba -> false | Tcont -> true

let is_statefull_kind expected_k =
  match expected_k with
  | Tdiscrete(true) | Tcont | Tproba -> true
  | Tdiscrete false | Tstatic _ | Tany -> false

(** Make a discrete sort. *)
let lift_to_discrete expected_k =
  match expected_k with
  | Tcont | Tdiscrete(true) -> Tdiscrete(true)
  | Tproba -> Tproba 
  | Tstatic _ | Tany | Tdiscrete _ -> expected_k

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
    | Tfun(_, _, ty_arg, ty_res) -> check ty_arg; check ty_res
    | Tvec(ty_arg, _) -> check ty_arg
    | Tlink(link) -> check link
  in check ty

(* remove useless dependence names from a type *)
(* Invariant: (n: t1) -k-> t2 => t1 -k-> t2 if n not in fv(t2) *)
let rec clear acc ({ t_desc = desc } as ty) =
  match desc with
  | Tvar -> ty, acc
  | Tproduct(ty_list) ->
     let ty_list, acc = Misc.map_fold clear acc ty_list in
     product(ty_list), acc
  | Tvec(ty_arg, size) ->
     let ty_arg, acc = clear acc ty_arg in
     let acc = fv_size acc size in
     vec ty_arg size, acc
  | Tfun(k, n_opt, ty_arg, ty_res) ->
     let ty_res, acc = clear acc ty_res in
     let n_opt, acc =
       match n_opt with
       | None -> None, acc
       | Some(n) ->
	  if S.mem n acc then Some(n), acc else None, S.remove n acc in
     let ty_arg, acc = clear acc ty_arg in
     funtype k n_opt ty_arg ty_res, acc
  | Tlink(ty_link) -> clear acc ty_link
  | Tconstr(gl, ty_list, abbrev) ->
     let clear_abbrev acc = function
       | Tnil -> Tnil, acc
       | Tcons(ty_list, ty) ->
	  let ty_list, acc = Misc.map_fold clear acc ty_list in
	  let ty, acc = clear acc ty in
	  Tcons(ty_list, ty), acc in
     let ty_list, acc = Misc.map_fold clear acc ty_list in
     let abbrev, acc = clear_abbrev acc !abbrev in
     constr gl ty_list (ref abbrev), acc

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
    | Tfun(_, _, ty_arg, ty_res) ->
	     ty.t_level <-
	       min (gen_ty is_gen ty_arg) (gen_ty is_gen ty_res)
    | Tvec(ty_arg, _) ->
       ty.t_level <- gen_ty is_gen ty_arg
    | Tlink(link) ->
       ty.t_level <- gen_ty is_gen link
  end;
  ty.t_level
      
(* main generalisation function *)
let gen non_expensive typ_body =
  list_of_typ_vars := [];
  ignore (gen_ty non_expensive typ_body);
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
    | Tfun(k, n_opt, ty_arg, ty_res) ->
       if level = generic
       then funtype k n_opt (copy ty_arg) (copy ty_res)
       else ty
    | Tvec(ty_arg, e) ->
       if level = generic
       then vec (copy ty_arg) e
       else ty

(** Compute the size of an array type [t]. *)
(* [t] is either a basic type float/int/bool or an nested *)
(* array of that *)
let size_of ty =
  let rec size_of ty =
    match ty.t_desc with
    | Tvar | Tproduct _ | Tfun _ -> assert false
    | Tlink(link) -> size_of link
    | Tconstr _ -> []
    | Tvec(ty, s) ->
       s :: (size_of ty) in
  List.rev (size_of ty)
	      
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
	| Tfun(k1, None, ty_arg1, ty_res1),
	  Tfun(k2, None, ty_arg2, ty_res2) ->
	   if k1 = k2 then
	     begin unify ty_arg1 ty_arg2; unify ty_res1 ty_res2 end
	   else raise Unify
	| Tfun(k1, Some(n1), ty_arg1, ty_res1),
	  Tfun(k2, Some(n2), ty_arg2, ty_res2) ->
	    unify ty_arg1 ty_arg2;
	    if k1 = k2 then
	      if Ident.compare n1 n2 = 0 then unify ty_res1 ty_res2
	      else
		let m = Ident.fresh (Ident.source n1) in
		let ty_res1 =
		  subst_in_type
		    (Env.singleton n1 (Tname(m))) ty_res1 in
		let ty_res2 =
		  subst_in_type
		    (Env.singleton n1 (Tname(m))) ty_res2 in
		unify ty_res1 ty_res2
	    else raise Unify
	| Tvec(ty1, si1), Tvec(ty2, si2) ->
	   unify ty1 ty2; equal_sizes si1 si2
	| _ -> raise Unify
				
and equal_sizes si1 si2 =
  match si1, si2 with
  | Tconst i1, Tconst i2 when i1 = i2 -> ()
  | Tname(n1), Tname(n2) when Ident.compare n1 n2 = 0 -> ()
  | Tglobal(gn1), Tglobal(gn2) when Lident.compare gn1 gn2 = 0 -> ()
  | Top(op1, si11, si12), Top(op2, si21, si22) when op1 = op2 ->
     equal_sizes si11 si21; equal_sizes si12 si22
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
  | Tfun(actual_k, n_opt, ty_arg, ty_res) ->
     actual_k, n_opt, ty_arg, ty_res
  | _ ->
     let ty_arg = new_var () in
     let ty_res = new_var () in
     unify ty (funtype expected_k None ty_arg ty_res);
     expected_k, None, ty_arg, ty_res

let filter_actual_arrow ty =
  let ty = typ_repr ty in
  match ty.t_desc with
  | Tfun(actual_k, n_opt, ty_arg, ty_res) ->
     actual_k, n_opt, ty_arg, ty_res
  | _ -> assert false

(* Splits the list of arguments of a function application *)
(* if [f e1 ... en] is an application with [f] of type
 * - t1 -S-> ... -S-> ti-1 -k1-> ... -kn-> tn+1
 * - returns [e1,...,ei] as static arguments; [ei+1;...; en] as non static 
 * - and the type of the result of the application *)
let rec split_arguments ty_fun e_list =
  match e_list with
  | [] -> [], [], ty_fun
  | e :: e_rest_list ->
     let k, _, _, ty_res = filter_actual_arrow ty_fun in
     match k with
     | Tstatic(true) ->
	let se_list, ne_list, ty_res = split_arguments ty_res e_rest_list in
	e :: se_list, ne_list, ty_res
     | _ -> [], e_list, ty_fun
			  
let filter_vec ty =
  let ty = typ_repr ty in
  match ty.t_desc with
  | Tvec(ty_arg, si) -> ty_arg, si
  | _ -> raise Unify

let type_of_combine () =
  funtype (Tstatic(false)) None
	  (new_var ())
	  (funtype (Tstatic(false)) None (new_var ()) (new_var ()))
		    		  
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

(** Is-it a combinatorial function? *)
let rec is_combinatorial n ty =
  if n = 0 then true
  else
    let ty = typ_repr ty in
    match ty.t_desc with
    | Tfun((Tdiscrete _ | Tcont | Tproba), _, _, _) -> false
    | Tfun(_, _, _, ty_res) -> is_combinatorial (n-1) ty_res
    | _ -> true

let rec res_type n ty =
  if n = 0 then ty
  else
    let ty = typ_repr ty in
    match ty.t_desc with
    | Tfun(_, _, _, ty_res) -> res_type (n-1) ty_res
    | _ -> assert false

let is_hybrid n ty =
  let ty = res_type n ty in
  let ty = typ_repr ty in
    match ty.t_desc with
    | Tfun(Tcont, _, _, _) -> true
    | _ -> false
	     
let is_probabilistic n ty =
  let ty = res_type n ty in
  let ty = typ_repr ty in
  match ty.t_desc with
  | Tfun(Tproba, _, _, _) -> true
  | _ -> false
	   
(** Is-it a node ? *)
let is_a_node_name lname =
  let { info = { value_typ = { typ_body = typ_body } } } = 
    Modules.find_value lname in
  match typ_body.t_desc with
    | Tfun((Tdiscrete(true) | Tcont), _, _, _) -> true | _ -> false

(** Is-it a function? *)
let is_a_function_name lname =
  let { info = { value_typ = { typ_body = ty } } } = 
    Modules.find_value lname in
  let ty = typ_repr ty in
  match ty.t_desc with
    | Tfun(Tany, _, _, _) -> true | _ -> false

(** Is-it a hybrid function? *)
let is_a_hybrid_node_name lname =
  let { info = { value_typ = { typ_body = ty } } } = 
    Modules.find_value lname in
  let ty = typ_repr ty in
  match ty.t_desc with
    | Tfun(Tcont, _, _, _) -> true | _ -> false

(* kind of a function type *)
let rec kind_of_funtype ty =
  let ty = typ_repr ty in
  match ty.t_desc with
  | Tfun(k, _, _, _) -> k | _ -> assert false
							
let kind_of_node_name lname =
  let { info = { value_typ = { typ_body = ty } } } = 
    Modules.find_value lname in
  kind_of_funtype ty

(* Does a type scheme contains static parameters *)
let noparameters { typ_vars = lvars; typ_body = typ_body } =
  let rec static { t_desc = desc } =
    match desc with
    | Tvar -> true
    | Tproduct(ty_list)| Tconstr(_, ty_list, _) -> List.for_all static ty_list
    | Tvec(ty_arg, _) -> static ty_arg
    | Tlink(ty_link) -> static ty_link
    | Tfun(Tstatic _, _, _, _) | Tfun(_, Some _, _, _) -> false
    | Tfun(_, _, ty_arg, ty_res) -> (static ty_arg) && (static ty_res) in
  static typ_body

(* Does a type scheme contains type variables *)
let nopolymorphism { typ_vars = lvars } = lvars = []
