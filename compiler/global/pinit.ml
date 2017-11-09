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
(* Printing an initialization type expression *)

open Format
open Pp_tools
open Misc
open Ident
open Definit

(* type variables are printed 'a, 'b,... *)
let type_name = new name_assoc_table int_to_alpha

let polarity = 
  function Punknown -> "" | Pplus -> "+" | Pminus -> "-" | Pplusminus -> "+-"

let useful i = if i.i_useful then "u" else ""
    
let level i = i.i_level
                
(* Print the causality *)
let rec init ff i = 
  match i.i_desc with
  | Izero -> fprintf ff "0"
  | Ione -> fprintf ff "1"
  | Ilink(link) -> init ff link
  | Ivar ->
    Format.fprintf
      ff "%s(%d)(%s)'%s"
      (useful i) (level i) (polarity i.i_polarity) (type_name#name i.i_index)
			   
let rec ptype prio ff ti =
  let priority = function | Iatom _ -> 3 | Iproduct _ -> 2 | Ifun _ -> 1 in
  let prio_current = priority ti in
  if prio_current < prio then fprintf ff "(";
  begin
    match ti with
    | Iatom(i) -> init ff i
    | Ifun(ty_arg, ty_res) ->
       Format.fprintf
	 ff
         "@[<hov2>%a ->@ %a@]" (ptype (prio_current + 1)) ty_arg
	 (ptype prio_current) ty_res
    | Iproduct(ty_list) ->
       print_list_r (ptype (prio_current + 1)) "" " *" "" ff ty_list
  end;
  if prio_current < prio then fprintf ff ")"  
				      
let ptype ff ti = ptype 0 ff ti
			
let relation ff i_list =
  let rel =
    List.fold_left
      (fun acc i ->
       match i.i_sup with | [] -> acc | sup_list -> (i, sup_list) :: acc)
      [] i_list in
  let rel = List.rev rel in
  let print ff (i, i_list) =
    Format.fprintf
      ff "@[%a < %a@]" init i (print_list_r init "" "," "") i_list in
  print_list_r print "{" ";" "}" ff rel
	       
(* print a type scheme *)
(* { a1 < a2,...,ak; ...; }. ti *)
let scheme ff { typ_vars = i_list; typ = ty } =
  Format.fprintf ff "@[<hov2>%a.@ %a@]" relation i_list ptype ty
                 
(* printing a declaration *)
let declaration ff f tys =
  type_name#reset;
  Format.fprintf ff "@[<hov2>val %s :@ @[%a@]@.@]" f scheme tys    
