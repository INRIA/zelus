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
		    
let info i =
  match i with
  | Cname(n) -> Ident.source n
  | Clast(n) -> "last " ^ (Ident.source n)
			       
let polarity = 
  function Punknown -> "" | Pplus -> "+" | Pminus -> "-" | Pplusminus -> "+-"
									   
(* Print the causality *)
let rec caus ff c = 
  match c.c_desc with
  | Clink(link) -> caus ff link
  | Cvar ->
     Format.fprintf ff "'%s" (type_name#name c.c_index)
				 
let caus_list ff c_list = print_list_r_empty caus "" "" "" ff c_list

(* Print the causality with the source name *)
let rec name ff c = 
  match c.c_desc with
  | Clink(link) -> name ff link
  | Cvar ->
     let index = c.c_index in
     let info = match c.c_info with None -> "_" | Some(i) -> info i in
     if !Misc.verbose then
       Format.fprintf ff "(%s:'%s)" info (type_name#name index)
     else Format.fprintf ff "%s" info

let rec typ priority ff = function
  | Catom(c) -> caus ff c
  | Cproduct(ty_list) ->
     (if priority >= 2
      then Format.fprintf ff "@[(%a)@]" else Format.fprintf ff "@[%a@]")
       (print_list_r (typ 2) "" " *" "") ty_list
       
(* print a set of dependences *)
let set ff s = Format.fprintf ff "@[{%a}@]" (fun ff s -> S.iter (caus ff) s) s
			      
(* Print the list of dependences ['a < 'b,...] *)
let relation ff rel =
  let print ff (c, c_sup) =
    Format.fprintf
      ff "@[%a < %a@]" caus c (print_list_r caus "" "," "") c_sup in
  print_list_r print "{" ";" "}" ff rel
	       
(* print a causality type signature *)
let signature ff
	      { typ_vars = c_list; typ_rel = rel;
		typ_args = ty_arg_list; typ_res = ty_res } = 
  (* print the argument type *)
  let arg_list ff = function
    | [] -> Format.fprintf ff "[]"
    | ty_arg_list -> 
       Format.fprintf
	 ff "@[%a@]" (print_list_r (typ 2) """ *""") ty_arg_list in
  Format.fprintf
    ff "@[%a.%a -> %a@]" relation rel arg_list ty_arg_list (typ 0) ty_res

   
(* prints a dependence cycle *)
let cycle ff c_list =
  (* remove intermediate nodes which are not associated to *)
  let rec print first ff l =
    match l with
    | [] -> assert false
    | [c] -> 
       Format.fprintf ff "%a < %a" name c name first
    | c1 :: ((c2 :: _) as l) -> 
       Format.fprintf ff "@[%a < %a;@ %a@]"
		      name c1 name c2 (print first) l in
  match c_list with
  | [] -> ()
  | first :: _ ->
     Format.fprintf ff "@[[%a]@]" (print first) c_list
		    
(* printing a declaration *)
let declaration ff f tys =
  type_name#reset;
  Format.fprintf ff "@[val %s : %a@.@]" f signature tys    
