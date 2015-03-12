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
(* Causality types and basic operations over these types *)

open Misc
open Ident
open Deftypes
open Defcaus
open Global
open Zelus

(** a set of causality names *)
module S = Set.Make(Defcaus)
(** and a module to represent the successors of a causality variable *)
module M = Map.Make(Defcaus)

let set c_list = List.fold_left (fun acc c -> S.add c acc) S.empty c_list
  
(* typing errors *)
exception Unify of Defcaus.t list

let new_var () = 
  { c_desc = Cvar; c_index = symbol#name; c_level = !binding_level;
    c_sup = []; c_useful = false; 
    c_polarity = Punknown; c_info = None }
let new_var_with_info n = 
  { c_desc = Cvar; c_index = symbol#name; c_level = !binding_level;
    c_sup = []; c_useful = false; 
    c_polarity = Punknown; c_info = Some(n) }
let product l = Cproduct(l)
let atom c = Catom(c)
let rec mem c l =
  match l with | [] -> false | c1 :: l -> (c.c_index = c1.c_index) || (mem c l)
let rec add c l = 
  match l with 
    | [] -> [c] 
    | c1 :: l1 -> if c.c_index = c1.c_index then l else c1 :: (add c l1)
let rec remove c l = 
  match l with 
    | [] -> [] 
    | c1 :: l1 -> if c.c_index = c1.c_index then l1 else c1 :: (remove c l1)
let rec union l1 l2 = 
  match l1, l2 with
    | [], l2 -> l2
    | l1, [] -> l1
    | x :: l1, l2 ->
        if mem x l2 then union l1 l2 else x :: union l1 l2

(* path compression *)
let rec crepr c =
  match c.c_desc with
    | Clink(c_son) ->
        let c_son = crepr c_son in
        c.c_desc <- Clink(c_son);
        c_son
    | _ -> c

(* equality of two nodes *)
let equal c1 c2 =
  let c1 = crepr c1 in
  let c2 = crepr c2 in
  c1.c_index = c2.c_index
		 
let rec mark_with_name n = function
  | Catom(c) -> atom(cmark_with_name n c)
  | Cproduct(ty_list) -> product(List.map (mark_with_name n) ty_list)
and cmark_with_name n c =
  let c = crepr c in
  c.c_info <- Some(Cname n); c

(* type variables of a type *)
let rec vars acc = function
  | Catom(c) -> add (crepr c) acc
  | Cproduct(ty_list) -> List.fold_left vars acc ty_list

(** Sets the polarity of a type. *)
let polarity pol c =
  match pol, c.c_polarity with
    | _, Punknown -> c.c_polarity <- pol
    | Punknown, polarity -> ()
    | _, polarity -> if pol <> polarity then c.c_polarity <- Pplusminus

(** check for cycles *)
let rec occur_check level index c =
  let rec check path c =
    match c.c_desc with
      | Cvar -> 
	  if c.c_level > level then c.c_level <- level;
	  if c.c_index = index 
	  then raise (Unify(List.rev (c :: path)))
	  else List.iter (check (c :: path)) c.c_sup
      | Clink(link) -> check path link
  in check [] c

(** Unification *)
let rec unify cunify left_tc right_tc =
  match left_tc, right_tc with
    | Cproduct(l1), Cproduct(l2) -> List.iter2 (unify cunify) l1 l2
    | Catom(c1), Catom(c2) -> cunify c1 c2
    | _ -> assert false

let rec cunify left_c right_c =
  if left_c == right_c then ()
  else 
    let left_c = crepr left_c in
    let right_c = crepr right_c in
    if left_c == right_c then ()
    else
      match left_c.c_desc, right_c.c_desc with
	| Cvar, Cvar ->
            List.iter (occur_check left_c.c_level left_c.c_index) right_c.c_sup;
	    List.iter (occur_check right_c.c_level right_c.c_index) left_c.c_sup;
	    left_c.c_desc <- Clink(right_c);
	    right_c.c_sup <- union left_c.c_sup right_c.c_sup
	| _ -> assert false

let rec ctype_before_ctype left_c right_c =
  let left_c = crepr left_c in
  let right_c = crepr right_c in
  match left_c.c_desc, right_c.c_desc with
    | Cvar, Cvar ->
        occur_check left_c.c_level left_c.c_index right_c;
        (* i1,...,in < i < j1,...,jk  with *)
        (* l1,...,lm < r < s1,...,sr *)
      left_c.c_sup <- add right_c left_c.c_sup
    | _ -> assert false

(* less than or equal is [c1 = c2 or c1 < c'1 and c'1 < c2] *)
let is_less_than_lists c1_list c2_list =
  let rec less_than_or_equal c1 c2 =
    if equal c1 c2 then true
    else match c1.c_desc with
      | Cvar -> List.exists (fun c1 -> less_than_or_equal c1 c2) c1.c_sup
      | Clink(c_link) -> less_than_or_equal c_link c2 in
  let less_than c1 c2 =
    if equal c1 c2 then false else less_than_or_equal c1 c2 in      
  List.exists
    (fun c1 -> List.exists (fun c2 -> less_than c1 c2) c2_list) c1_list
      
(* the main entry *)
let type_before_type = unify ctype_before_ctype
  
(* ordering between two environments. This is done structurally *)
(* for local names defined in [right_env] *)
(* returns the environment in which local names has been removed *)
let env_structurally_before_env left_env right_env =
  let before x left_opt right_opt =
    match left_opt, right_opt with
    | None, _ -> None
    | Some(entry), None -> Some(entry)
    | Some { t_typ = tc1 }, Some { t_typ = tc2 } -> 
       type_before_type tc1 tc2; None in
  Env.merge before left_env right_env

    
(* take a type [tc] and a causality [c] and returns a new type [tc'[c]] *)
(* with [tc < tc'[c]] *)
let rec after tc c =
  match tc with
    | Cproduct(l) -> Cproduct(List.map (fun tc -> after tc c) l)
    | Catom(left_c) -> Catom(afterc left_c c)
and afterc left_c c = 
  ctype_before_ctype left_c c; c
    
(* Compute the sup of two types *)
let rec sup left_tc right_tc =
  match left_tc, right_tc with
  | Cproduct(l1), Cproduct(l2) when List.length l1 = List.length l2 -> 
     Cproduct(List.map2 sup l1 l2)
  | Catom(c1), Catom(c2) -> Catom(supc c1 c2)
  | _ -> assert false

and supc left_c right_c =
  let left_c = crepr left_c in
  let right_c = crepr right_c in
  let c = new_var () in
  left_c.c_sup <- add c left_c.c_sup;
  right_c.c_sup <- add c right_c.c_sup;
  c

let sup_list tc_list = 
  match tc_list with
  | [] -> assert false
  | hd :: tl -> List.fold_left sup hd tl

(* Computes the sup of two typing environments *)
let supenv left_env right_env =
  let sup x left_opt right_opt =
    match left_opt, right_opt with
    | None, None -> None
    | None, Some(entry) -> Some(entry)
    | Some(entry), None -> Some(entry)
    | Some({ t_typ = tc1; t_last = is_last1 }), 
      Some({ t_typ = tc2; t_last = is_last2 }) -> 
       Some({ t_typ = sup tc1 tc2; t_last = is_last1 || is_last2 }) in
  Env.merge sup left_env right_env

let supenv_list env_list = List.fold_left supenv Env.empty env_list
  

let rec copy c = function
  | Cproduct(tc_list) -> product (List.map (copy c) tc_list)
  | Catom(c_atom) -> atom c

let append_list env_list = List.fold_left Env.append Env.empty env_list

(** Synchronise a type *)
let synchronise left_c tc =
  let rec csynchronise  right_c =
    let right_c = crepr right_c in
    match right_c.c_desc with
      | Cvar -> cunify left_c right_c
      | Clink(link) -> csynchronise link
  and synchronise tc =
    match tc with
      | Cproduct(tc_list) -> List.iter synchronise tc_list
      | Catom(right_c) -> csynchronise right_c in
  synchronise tc

(** Computing a causality type from a type *)
let skeleton new_var ty =
  let rec skeleton ty =
    match ty.t_desc with
    | Tvar -> atom (new_var ())
    | Tproduct(ty_list) -> product (List.map skeleton ty_list)
    | Tconstr(_, ty_list, _) -> atom (new_var ())
    | Tlink(ty) -> skeleton ty in
  skeleton ty

let skeleton_with_name n ty =
  skeleton (fun () -> new_var_with_info (Cname(n))) ty

let skeleton ty = skeleton new_var ty

let rec skeleton_on_c c ty =
  match ty.t_desc with
    | Tvar -> atom c
    | Tproduct(ty_list) -> product (List.map (skeleton_on_c c) ty_list)
    | Tconstr(_, ty_list, _) -> atom c
    | Tlink(ty) -> skeleton_on_c c ty

(* [last x] depends on nothing *)
let rec last tc =
  let rec lastc c =
    match c.c_desc with
      | Cvar -> new_var ()
      | Clink(link) -> lastc link in
  match tc with
    | Cproduct(l) -> Cproduct(List.map last l)
    | Catom(c) -> Catom(lastc c)

(** Build a skeleton from a causality type *)
let rec copy_on_c c_left tc =
  match tc with
    | Cproduct(tc_list) -> product (List.map (copy_on_c c_left) tc_list)
    | Catom(c) -> atom (ccopy_on_c c_left c)

and ccopy_on_c c_left c =
  match c.c_desc with
    | Cvar -> c_left
    | Clink(link) -> ccopy_on_c c_left link
                      
(** Simplification of types *)
(* Mark useful/useless variables and returns them *)
let rec mark pol acc tc =
  let rec cmark acc c =
    let c = crepr c in
    match c.c_desc with
      | Cvar -> 
	  c.c_useful <- true;
	  polarity pol c;
	  S.add c acc
      | Clink(link) -> cmark acc link in
  match tc with
    | Cproduct(tc_list) -> List.fold_left (mark pol) acc tc_list
    | Catom(c) -> cmark acc c

(* we compute IO sets [see Pouzet and Raymond, EMSOFT'09] *)
(* IO(c) = { i / i in I /\ i <_O c } and i <_O c iff O(c) subset O(i) *)
(* Partition according to IO, i.e., two variables with the same IO *)
(* get the same representative *)
let is_an_output c =
  c.c_useful && ((c.c_polarity = Pplus) || (c.c_polarity = Pplusminus))
		  
(* compute the set of inputs and outputs *)
let rec ins_and_outs c (inputs, outputs) =
  match c.c_desc with
  | Clink(link) -> ins_and_outs link (inputs, outputs)
  | Cvar ->
     match c.c_polarity with
     | Pplus -> inputs, S.add c outputs
     | Pminus -> S.add c inputs, outputs
     | Pplusminus -> S.add c inputs, S.add c outputs
     | _ -> inputs, outputs
		      
(* build O(c) *)
let rec out c =
  let rec outrec acc c =
    let c = crepr c in
    match c.c_desc with
    | Clink(link) -> outrec acc link
    | Cvar ->
       let acc = if is_an_output c then S.add c acc else acc in
       List.fold_left outrec acc c.c_sup in
  outrec S.empty c  

let simplify c_set =
  (* is-it an output? *)
  let inputs, outputs = S.fold ins_and_outs c_set (S.empty, S.empty) in
  let inputs_outputs = S.union inputs outputs in

  (* build the association table [i, O(i)] for every i in I and O *)
  let o_table =
    S.fold (fun i acc -> M.add i (out i) acc) inputs M.empty in
  let o_table =
    S.fold (fun i acc -> M.add i (out i) acc) outputs o_table in
  
  (* compute io(c) *)
  let rec io c =
    let o = M.find c o_table in
    S.fold
      (fun i' acc ->
       let o' = M.find i' o_table in
       if S.subset o o' then S.add i' acc else acc)
      inputs S.empty in
  
  (* then the table of io for every input/output *)
  let io_table = S.fold (fun i acc -> M.add i (io i) acc) inputs M.empty in
  let io_table = S.fold (fun o acc -> M.add o (io o) acc) outputs io_table in

  (* finally, the dependence relation is that of [io], i.e., *)
  (* c1 < c2 iff io(c1) subset io(c2) *)
  (* moreover, variables are partitioned according to [io], i.e., *)
  (* [c1 eq c2 iff io(c1) = io(c2)] *)
  let set c_left c_right = (crepr c_left).c_desc <- Clink(c_right) in
  let less c_left c_right =
    let c_left = crepr c_left in c_left.c_sup <- add c_right c_left.c_sup in
  S.iter (fun c -> c.c_sup <- []) inputs_outputs;
  S.iter
    (fun i -> 
      let io_of_i = M.find i io_table in
      S.iter 
	(fun o ->
	  let io_of_o = M.find o io_table in
	  if not (equal i o)
	  then if S.subset io_of_i io_of_o then
		 if S.compare io_of_i io_of_o = 0 then set i o
		 else less i o)
	outputs)
    inputs
    
(* TEMPORARY SOLUTION for testing: *)
(* eliminate doublons, e.g., [c < b, b] and dependences to variables *)
(* which are not input or outputs *)

(*
let simplify c_set =
  let rec remove_useless_variables c_set = S.iter remove_useless c_set 
  and remove_useless c = 
    let c = crepr c in
    c.c_sup <- useful_list [] c.c_sup
  and useful_list acc l = List.fold_left useful acc l
  and useful acc c_right =
    let c_right = crepr c_right in
    match c_right.c_desc with
    | Cvar -> 
       if c_right.c_useful then add c_right acc
       else useful_list acc c_right.c_sup
    | Clink(link) -> useful acc link in
  remove_useless_variables c_set
  *)
			   
(* let simplify c_set = () *)

(** Generalisation of a type *)
(* the level of generalised type variables *)
(* is set to [generic]. Returns [generic] when a sub-term *)
(* can be generalised *)

let list_of_vars = ref []

let rec gen tc =
  match tc with
    | Cproduct(tc_list) -> List.iter gen tc_list
    | Catom(c) -> ignore (cgen c)

and cgen c =
  let c = crepr c in
  match c.c_desc with
    | Cvar ->
        if c.c_level > !binding_level
	then 
	  begin
	    c.c_level <- generic;
	    let level = gen_set c.c_sup in
	    c.c_level <- level;
	    if level = generic then list_of_vars := c :: !list_of_vars
	  end;
        c.c_level
    | Clink(link) -> cgen link
    
and gen_set l = List.fold_left (fun acc c -> max (cgen c) acc) generic l

(** Main generalisation function *)
let generalise tc_arg_list tc_res =
  list_of_vars := [];
  (* we compute useful variables *)
  let c_set = List.fold_left (mark Pminus) S.empty tc_arg_list in
  let c_set = mark Pplus c_set tc_res in
  (* type simplification *)
  simplify c_set;
  List.iter (fun tc -> ignore (gen tc)) tc_arg_list;
  ignore (gen tc_res);
  { typ_vars = !list_of_vars; typ_args = tc_arg_list; typ_res = tc_res }

(** Instantiation of a type *)
(* save and cleanup links *)
let links = ref []
    
let save link = links := link :: !links
let cleanup () = List.iter (fun c -> c.c_desc <- Cvar) !links; links := []

(* instanciation *)
let instance tc_arg_list tc_res =
  let rec copy tc =
    match tc with
      | Cproduct(tc_list) -> product (List.map copy tc_list)
      | Catom(c) -> atom (ccopy c)
	
  and ccopy c =
    match c.c_desc with
      | Cvar ->
          if c.c_level = generic
	  then
	    let v = new_var () in
	    c.c_desc <- Clink(v);
            save c;
            v
          else c
      | Clink(link) -> if c.c_level = generic then link else ccopy link in
  
  let tc_arg_list = List.map copy tc_arg_list in
  let tc_res = copy tc_res in
  cleanup ();
  tc_arg_list, tc_res

(* check that [tc] is of the form [tc1;...;tc_arity] *)
let filter_product arity tc =
  match tc with
    | Cproduct(l) when List.length l = arity -> l
    | _ -> assert false

(** Type instance *)
let instance { value_caus = tcs_opt; value_typ = { typ_body = typ_body } } =
  (* build a default signature *)
  let signature ty_arg_list ty_res =
    let c = new_var () in
    List.map (skeleton_on_c c) ty_arg_list, skeleton_on_c c ty_res in
  let ty_arg_list, ty_res = 
    match typ_body with
    | Tvalue _ -> assert false
    | Tsignature(_, _, ty_arg_list, ty_res) -> ty_arg_list, ty_res in
  match tcs_opt with
    | None -> 
       (* if no causality information has been entered, a default one is built *)
       signature ty_arg_list ty_res
    | Some({ typ_args = tc_causality_arg_list; typ_res = tc_causality_res }) -> 
        instance tc_causality_arg_list tc_causality_res

