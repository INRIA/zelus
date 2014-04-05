(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
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
open Deftypes
open Defcaus
open Global
open Zelus

(** A module to represent sets of causality variables *)
module S = Set.Make(Defcaus)

(** and a module to represent the successors of a causality variable *)
module M = Map.Make(Defcaus)

let set c_list = List.fold_left (fun acc c -> S.add c acc) S.empty c_list
  
(** An entry in the type environment *)
type tentry = 
    { t_typ: Defcaus.typ; (* the causality type of x *)
      t_der: bool; (* in case [x] is a derivative *)
      t_next: bool; (* [x] is modified through [next x = ...] only *) 
    }

(* typing errors *)
exception Unify of Defcaus.info list

(* Accumulate in a list the sequence of names involved in a cycle *)
let info c acc = match c with | None -> acc | Some(n) -> n :: acc

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
let pair c1 c2 = 
  { c_desc = Cpair(c1, c2); c_index = symbol#name; c_level = generic;
    c_sup = []; c_useful = false; c_polarity = Punknown; c_info = None }
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

(* erase every occurrence of a given variable from the sups *)
let rec erase_sups c c_list = List.fold_left (erase c) [] c_list

(* [erase c acc c_into] returns either [acc] or [c_into :: acc] *)
(* if [c <> c_into] and remove all occurrences of [c] into the *)
(* sups of [c_into] *)
and erase c acc c_into =
  let c_into = crepr c_into in
  let c_sup = erase_sups c c_into.c_sup in
  c_into.c_sup <- c_sup;
  if c.c_index = c_into.c_index then acc else c_into :: acc
  
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
	  then raise (Unify(List.rev (info c.c_info path)))
	  else List.iter (check (info c.c_info path)) c.c_sup
      | Cpair(c1, c2) -> check path c1; check path c2
      | Clink(link) -> check path link
  in check [] c

(** Unification *)
let rec unify cunify left_ty right_ty =
  match left_ty, right_ty with
    | Cproduct(l1), Cproduct(l2) -> List.iter2 (unify cunify) l1 l2
    | Catom(c1), Catom(c2) -> cunify c1 c2
    | _ -> raise (Unify [])

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
	| Cpair(c1, c2), Cpair(c11, c22) ->
            cunify c1 c11; cunify c2 c22
	| _ -> raise (Unify [])

let rec cless left_c right_c =
  let left_c = crepr left_c in
  let right_c = crepr right_c in
  match left_c.c_desc, right_c.c_desc with
    | Cvar, Cvar ->
        occur_check left_c.c_level left_c.c_index right_c;
        (* i1,...,in < i < j1,...,jk  with  *)
        (* l1,...,lm < r < s1,...,sr *)
      left_c.c_sup <- add right_c left_c.c_sup
    | Cpair(c1, c2), Cpair(c11, c22) ->
        cless c1 c11; cless c2 c22
    | _ -> raise (Unify [])

(* the main entry *)
let less = unify cless
let unify = unify cunify

(** Synchronise a type *)
let synchronise left_c ty =
  let rec csynchronise  right_c =
    let right_c = crepr right_c in
    match right_c.c_desc with
      | Cvar -> cunify left_c right_c
      | Cpair(c1, c2) -> csynchronise c1; csynchronise c2
      | Clink(link) -> csynchronise link
  and synchronise ty =
    match ty with
      | Cproduct(ty_list) -> List.iter synchronise ty_list
      | Catom(right_c) -> csynchronise right_c in
  synchronise ty

(** Computing a causality type from a type *)
let skeleton n ty =
  let n = Cname(n) in
  let rec skeleton ty =
    match ty.t_desc with
      | Tvar -> atom (new_var_with_info n)
      | Tproduct(ty_list) -> product (List.map skeleton ty_list)
      | Tconstr(_, ty_list, _) -> atom (new_var_with_info n)
      | Tlink(ty) -> skeleton ty in
  skeleton ty

let rec skeleton_on_c c ty =
  match ty.t_desc with
    | Tvar -> atom c
    | Tproduct(ty_list) -> product (List.map (skeleton_on_c c) ty_list)
    | Tconstr(_, ty_list, _) -> atom c
    | Tlink(ty) -> skeleton_on_c c ty

(* [last x] depends on nothing *)
let rec last ty =
  let rec lastc c =
    match c.c_desc with
      | Cvar -> new_var ()
      | Cpair(c1, c2) -> pair (new_var ()) c2
      | Clink(link) -> lastc link in
  match ty with
    | Cproduct(l) -> Cproduct(List.map last l)
    | Catom(c) -> Catom(lastc c)

(** Build a skeleton from a causality type *)
let rec copy_on_c c_left ty =
  match ty with
    | Cproduct(ty_list) -> product (List.map (copy_on_c c_left) ty_list)
    | Catom(c) -> atom (ccopy_on_c c_left c)

and ccopy_on_c c_left c =
  match c.c_desc with
    | Cvar -> c_left
    | Clink(link) -> ccopy_on_c c_left link
    | Cpair(c1, c2) -> pair (ccopy_on_c c_left c1) (ccopy_on_c c_left c2)
                  
(** Simplification of types *)
(* Mark useful/useless variables and returns them *)
let rec mark pol acc ty =
  let rec cmark acc c =
    let c = crepr c in
    match c.c_desc with
      | Cvar -> 
	  c.c_useful <- true;
	  polarity pol c;
	  S.add c acc
      | Clink(link) -> cmark acc link
      | Cpair(c1, c2) -> 
	 cmark (cmark acc c1) c2 in
  match ty with
    | Cproduct(ty_list) -> List.fold_left (mark pol) acc ty_list
    | Catom(c) -> cmark acc c

(* we compute IO sets [see Pouzet and Raymond, EMSOFT'09] *)
(* IO(c) = { i / i in I /\ i <_O c } and i <_O c iff O(c) subset O(i) *)
(* Partition according to IO, i.e., two variables with the same IO *)
(* get the same representative *)
let simplify c_set =
  (* is-it an output? *)
  let is_an_output c =
    c.c_useful && ((c.c_polarity = Pplus) || (c.c_polarity = Pplusminus)) in

  (* equality of two nodes *)
  let equal c1 c2 =
    let c1 = crepr c1 in let c2 = crepr c2 in
    c1.c_index = c2.c_index in
  (* compute the set of inputs and outputs *)
  let rec ins_and_outs c (inputs, outputs) =
    match c.c_desc with
      | Clink(link) -> ins_and_outs link (inputs, outputs)
      | Cpair(c1, c2) -> ins_and_outs c1 (ins_and_outs c2 (inputs, outputs))
      | Cvar ->
	  match c.c_polarity with
	    | Pplus -> inputs, S.add c outputs
	    | Pminus -> S.add c inputs, outputs
	    | Pplusminus -> S.add c inputs, S.add c outputs
	    | _ -> inputs, outputs in
  let inputs, outputs = S.fold ins_and_outs c_set (S.empty, S.empty) in
  let inputs_outputs = S.union inputs outputs in

  (* build O(c) *)
  let rec out c =
    let rec outrec acc c =
      let c = crepr c in
      match c.c_desc with
	| Clink(link) -> outrec acc link
	| Cpair(c1, c2) -> outrec (outrec acc c1) c2
	| Cvar ->
	    let acc = if is_an_output c then S.add c acc else acc in
	    List.fold_left outrec acc c.c_sup in
    outrec S.empty c in
  
  (* build the association table [i, O(i)] for every c in I *)
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
  let io_table = S.fold (fun i acc-> M.add i (io i) acc) inputs M.empty in
  let io_table = S.fold (fun o acc -> M.add o (io o) acc) outputs io_table in

  (* finally, the dependence relation is that of [io], i.e., *)
  (* c1 < c2 iff io(c1) subset io(c2) *)
  (* moreover, variables are partitioned according to [io], i.e., *)
  (* [c1 eq c2 iff io(c1) = io(c2)] *)
  S.iter (fun c -> c.c_sup <- []) inputs_outputs;
  S.iter
    (fun i -> 
      let io_of_i = M.find i io_table in
      S.iter 
	(fun o ->
	  let io_of_o = M.find o io_table in
	  if not (equal i o)
	  then if S.subset io_of_i io_of_o
	    then if S.compare io_of_i io_of_o = 0 then o.c_desc <- Clink(i)
	      else i.c_sup <- add o i.c_sup)
	outputs)
    inputs

(** Generalisation of a type *)
(* the level of generalised type variables *)
(* is set to [generic]. Returns [generic] when a sub-term *)
(* can be generalised *)

let list_of_vars = ref []

let rec gen ty =
  match ty with
    | Cproduct(ty_list) -> List.iter gen ty_list
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
    | Cpair(c1, c2) -> min (cgen c1) (cgen c2)

and gen_set l = List.fold_left (fun acc c -> max (cgen c) acc) generic l

(** Main generalisation function *)
let generalise ty_arg_list ty_res =
  list_of_vars := [];
  (* we compute useful variables *)
  let c_set = List.fold_left (mark Pminus) S.empty ty_arg_list in
  let c_set = mark Pplus c_set ty_res in
  (* type simplification *)
  simplify c_set;
  List.iter (fun ty -> ignore (gen ty)) ty_arg_list;
  ignore (gen ty_res);
  { typ_vars = !list_of_vars; typ_args = ty_arg_list; typ_res = ty_res }

(** Instantiation of a type *)
(* save and cleanup links *)
let links = ref []
    
let save link = links := link :: !links
let cleanup () = List.iter (fun c -> c.c_desc <- Cvar) !links; links := []

(* instanciation *)
let instance ty_arg_list ty_res =
  let rec copy ty =
    match ty with
      | Cproduct(ty_list) -> product (List.map copy ty_list)
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
      | Clink(link) ->
          if c.c_level = generic then link else ccopy link
      | Cpair(c1, c2) ->
          pair (ccopy c1) (ccopy c2) in
            
  let ty_arg_list = List.map copy ty_arg_list in
  let ty_res = copy ty_res in
  cleanup ();
  ty_arg_list, ty_res

(** Type instance *)
(* From the caller, outputs of an atomic node depends on all of its inputs *)
(* This double check is useless at to moment because the declaration of an *)
(* atomic function produce the identity causality *)
let instance { value_atomic = is_atomic; 
	       value_caus = tys_opt; value_typ = { typ_body = typ_body } } =
  (* build a default signature *)
  let signature ty_arg_list ty_res =
    let c = new_var () in
    List.map (skeleton_on_c c) ty_arg_list, skeleton_on_c c ty_res in
  let ty_arg_list, ty_res = 
    match typ_body with
    | Tvalue _ -> assert false
    | Tsignature(_, _, ty_arg_list, ty_res) -> ty_arg_list, ty_res in
  match tys_opt with
    | None -> 
       (* if no causality information has been entered, a default one is built *)
       signature ty_arg_list ty_res
    | Some({ typ_args = ty_causality_arg_list; typ_res = ty_causality_res }) -> 
        if is_atomic then signature ty_arg_list ty_res
	else instance ty_causality_arg_list ty_causality_res

module Printer = struct
  open Format
  open Pp_tools

  (* type variables are printed 'a, 'b,... *)
  let type_name = new name_assoc_table int_to_alpha

  let name ff index = fprintf ff "'%s" (type_name#name index)

  let polarity = 
    function Punknown -> "" | Pplus -> "+" | Pminus -> "-" | Pplusminus -> "+-"
 
  let rec caus ff c = 
    match c.c_desc with
      | Cvar -> name ff c.c_index; fprintf ff "%s" (polarity c.c_polarity)
      | Cpair(c1, c2) -> fprintf ff "@[%a+%a@]" caus c1 caus c2
      | Clink(link) -> caus ff link

  let rec typ priority ff = function
    | Catom(c) -> caus ff c
    | Cproduct(ty_list) ->
        (if priority >= 2 then fprintf ff "@[(%a)@]" else fprintf ff "@[%a@]")
	  (print_list_r (typ 2) "" " *" "") ty_list

  (* collect the list of dependences ['a < 'b,...] *)
  let relation ff c_list =
    let collect acc c =
      if c.c_sup = [] then acc
      else (c, c.c_sup) :: acc in
    let print ff (c, c_sup) =
      fprintf ff "@[%a < %a@]" caus c (print_list_r caus "" "," "") c_sup in
    let c_sup_list = List.fold_left collect [] c_list in
    print_list_r print "{" ";" "}" ff c_sup_list
      
  let signature ff
      { typ_vars = c_list; typ_args = ty_arg_list; typ_res = ty_res } = 
    (* print the argument type *)
    let arg_list ff = function
      | [] -> fprintf ff "[]"
      | ty_arg_list -> 
          fprintf ff "@[%a@]" (print_list_r (typ 2) """ *""") ty_arg_list in
    fprintf ff "@[%a.%a -> %a@]" relation c_list arg_list ty_arg_list
      (typ 0) ty_res

  (* prints a dependence cycle *)
  let cycle ff n_list =
    let info ff i =
      match i with
	| Cname(n) -> fprintf ff "%s" (Ident.source n)
	| Clast(n) -> fprintf ff "last %s" (Ident.source n) in
    let rec print first ff l =
      match l with
	| [] -> ()
	| [n] -> 
            fprintf ff "%a --> %a" info n info first
	| n1 :: ((n2 :: _) as l) -> 
            if n1 <> n2 then
              fprintf ff "@[%a --> %a@ %a@]" info n1 info n2 (print first) l
            else print first ff l in
    match n_list with
      | [] -> ()
      | first :: _ -> 
	  fprintf ff "@[Here is a an example of a cycle:@,[%a]@.@]" 
	    (print first) n_list
      
  (* printing a declaration *)
  let declaration ff f tys =
    type_name#reset;
    fprintf ff "@[val %s : %a@.@]" f signature tys    
end
