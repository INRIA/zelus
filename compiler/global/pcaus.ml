(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* Printing a causality expression *)

open Format
open Pp_tools
open Misc
open Ident
open Defcaus
       
(** a set of causality names *)
module S = Set.Make(Defcaus)
(** and a module to represent the successors of a causality variable *)
module M = Map.Make(Defcaus)

(* type variables are printed 'a, 'b,... *)
let type_name = new name_assoc_table int_to_alpha
		    
let name ff index =
  if !Misc.verbose then
    Format.fprintf ff "'%s(%d)" (type_name#name index) index
  else Format.fprintf ff "'%s" (type_name#name index)
		      
let info ff i =
  match i with
  | Cname(n) -> Format.fprintf ff "%s" (Ident.source n)
  | Clast(n) -> Format.fprintf ff "last %s" (Ident.source n)
			       
let polarity = 
  function Punknown -> "" | Pplus -> "+" | Pminus -> "-" | Pplusminus -> "+-"
									   
let rec caus ff c = 
  match c.c_desc with
  | Cvar ->
     name ff c.c_index;
     if !Misc.verbose
     then begin
	 begin match c.c_info with 
	       | None -> () | Some(i) -> Format.fprintf ff "(%a)" info i end;
	 Format.fprintf ff "%s" (polarity c.c_polarity) end
  | Clink(link) -> caus ff link

let caus_list ff c_list = print_list_r_empty caus "" "" "" ff c_list
		     
let rec typ priority ff = function
  | Catom(c) -> caus ff c
  | Cproduct(ty_list) ->
     (if priority >= 2
      then Format.fprintf ff "@[(%a)@]" else Format.fprintf ff "@[%a@]")
       (print_list_r (typ 2) "" " *" "") ty_list
       
(* print a set of dependences *)
let set ff s = Format.fprintf ff "@[{%a}@]" (fun ff s -> S.iter (caus ff) s) s
			      
let map ff m =
  let one ff c s = Format.fprintf ff "@[%a -> %a@]@," caus c set s in
  Format.fprintf ff "@[{%a}@]" (fun ff m -> M.iter (one ff) m) m
		 
(* computes the set of constraints ['a < 'a_1,..., 'a_n] *)
(* for variables ['a] not already in [set] *)
let rec collect (set, acc) c =
  if c.c_sup = [] || S.mem c set then set, acc
  else List.fold_left collect (S.add c set, (c, c.c_sup) :: acc) c.c_sup
		      
(* collect the list of dependences ['a < 'b,...] *)
let relation ff c_list =
  let print ff (c, c_sup) =
    Format.fprintf
      ff "@[%a < %a@]" caus c (print_list_r caus "" "," "") c_sup in
  let _, c_sup_list = List.fold_left collect (S.empty, []) c_list in
  print_list_r print "{" ";" "}" ff c_sup_list
	       
let signature ff
	      { typ_vars = c_list; typ_args = ty_arg_list; typ_res = ty_res } = 
  (* print the argument type *)
  let arg_list ff = function
    | [] -> Format.fprintf ff "[]"
    | ty_arg_list -> 
       Format.fprintf
	 ff "@[%a@]" (print_list_r (typ 2) """ *""") ty_arg_list in
  Format.fprintf
    ff "@[%a.%a -> %a@]" relation c_list arg_list ty_arg_list (typ 0) ty_res
		 
(* prints a dependence cycle *)
let cycle ff c_list =
  (* remove intermediate nodes which are not associated to *)
  (* a concrete name in the program *)
  let rec keep { c_desc = desc; c_info = info } acc =
    match desc with
    | Clink(c) -> keep c acc
    | Cvar -> match info with | None -> acc | Some(name) -> name :: acc in
  let rec print first ff l =
    match l with
    | [] -> ()
    | [n] -> 
       Format.fprintf ff "%a --> %a" info n info first
    | n1 :: ((n2 :: _) as l) -> 
       Format.fprintf ff "@[%a --> %a@ %a@]" info n1 info n2 (print first) l in
  let n_list = List.fold_right keep c_list [] in
  match n_list with
  | [] -> ()
  | first :: _ ->
     Format.fprintf ff "@[[%a]@]" (print first) n_list
		    
(* printing a declaration *)
let declaration ff f tys =
  type_name#reset;
  Format.fprintf ff "@[val %s : %a@.@]" f signature tys    
