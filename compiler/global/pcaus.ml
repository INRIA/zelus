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

(* Printing a causality type expression *)

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
let useful u = if u then "u" else ""
let level l = string_of_int l

let extra { c_polarity = p; c_useful = u; c_level = l; c_index = i } =
  if !Misc.verbose
  then polarity p ^ useful u ^ level l ^ "(" ^ (string_of_int i) ^ ")" else ""

  
(* Print the causality *)
let rec caus ff c = 
  match c.c_desc with
  | Clink(link) -> caus ff link
  | Cvar ->
     Format.fprintf ff "%s'%s" (extra c) (type_name#name c.c_index)
				 
let caus_list ff c_list = print_list_r_empty caus "" "" "" ff c_list

(* Print the causality with the source name *)
let rec caus_by_name ff c = 
  match c.c_desc with
  | Clink(link) -> caus_by_name ff link
  | Cvar ->
     let index = c.c_index in
     match c.c_info with
     | None -> Format.fprintf ff "%s" (type_name#name index)
     | Some(i) -> Format.fprintf ff "%s at '%s" (info i) (type_name#name index)
                    
let rec ptype prio ff tc =
  let priority = function | Catom _ -> 3 | Cproduct _ -> 2 | Cfun _ -> 1 in
  let prio_current = priority tc in
  if prio_current < prio then fprintf ff "(";
  begin
    match tc with
    | Catom(c) -> caus ff c
    | Cfun(ty_arg, ty_res) ->
      Format.fprintf ff
        "@[<hov2>%a ->@ %a@]" (ptype (prio_current + 1)) ty_arg
	(ptype prio_current) ty_res
    | Cproduct(ty_list) ->
      print_list_r (ptype (prio_current + 1)) "" " *" "" ff ty_list
  end;
  if prio_current < prio then fprintf ff ")"  
      
let ptype ff tc = ptype 0 ff tc
    
(* print a set of dependences *)
let set ff s = Format.fprintf ff "@[{%a}@]" (fun ff s -> S.iter (caus ff) s) s
    
(* Print the list of dependences ['a < 'b,...] *)
(* doublons have normally be removed by the type generalisation *)
let relation ff rel =
  let print ff (c, c_sup) =
    Format.fprintf
      ff "@[%a < %a@]" caus c (print_list_r caus "" "," "") c_sup in
  print_list_r print "{" ";" "}" ff rel
    
(* print a causality type signature *)
let scheme ff { typ_rel = rel; typ = ty } = 
  Format.fprintf ff "@[<hov2>%a.@ %a@]" relation rel ptype ty
    
(* prints a dependence cycle *)
let cycle with_info ff c_list =
  let caus = if with_info then caus_by_name else caus in
  let rec print first ff l =
    match l with
    | [] -> Format.fprintf ff "@[%a < %a@]" caus first caus first
    | [c] -> Format.fprintf ff "@[%a < %a@]" caus c caus first
    | c1 :: ((c2 :: _) as l) -> 
      Format.fprintf
        ff
        "@[<hov>%a < %a;@ %a@]" caus c1 caus c2 (print first) l in
  match c_list with
  | [] -> () (* assert false *)
  | (first :: _) as l -> print first ff l
                           
(* printing a declaration *)
let declaration ff f tys =
  type_name#reset;
  Format.fprintf ff "@[<hov2>val %s :@ @[%a@]@.@]" f scheme tys    
    
