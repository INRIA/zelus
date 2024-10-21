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

(* Printing a type expression *)

open Format
open Pp_tools
open Misc
open Lident
open Global
open Modules
open Deftypes
open Misc
   
(* the long name of an ident is printed       *)
(* if it is different from the current module *)
let print_qualid ff qualid = 
  Lident.fprint_t ff (Initial.short (currentname (Modname(qualid))))

(* type variables are printed 'a, 'b,... *)
let type_name = new Genames.name_assoc_table Genames.int_to_alpha

(* generic printing of a list *)
let print_list print_el sep ff l =
  let rec printrec ff l =
    match l with
      [] -> ()
    | [x] -> print_el ff x
    | x::l -> fprintf ff "@[%a%s@ %a@]" print_el x sep printrec l
  in
    printrec ff l

let arrow_tostring = function 
  | Tfun(k) ->
     (match k with Tconst -> "-V->" | Tstatic -> "-S->" | Tany -> "-A->")
  | Tnode(k) ->
     (match k with Tdiscrete -> "-D->" | Tcont -> "-C->")

let print_size ff si =
  let operator = function Splus -> "+" | Sminus -> "-" | Smult -> "*" in
  let priority = function Splus -> 0 | Sminus -> 1 | Smult -> 3 in
  let priority si =
    match si with
    | Svar _ | Sint _ -> 3 | Sfrac _ -> 2 | Sop(op, _, _) -> priority op in
  let rec printrec prio ff si =
    let prio_s = priority si in
    if prio > prio_s then fprintf ff "(";
    begin match si with
    | Svar(x) -> fprintf ff "%s" (Ident.name x)
    | Sint(i) -> fprintf ff "%d" i
    | Sfrac { num; denom } ->
       fprintf ff "@[%a/%d]@]" (printrec prio_s) num denom
    | Sop(op, si1, si2) ->
       fprintf ff "@[%a %s %a@]"
	 (printrec prio_s) si1 (operator op) (printrec prio_s) si2;
    end;
    if prio > prio_s then fprintf ff ")" in       
  printrec 0 ff si

let rec print prio ff { t_desc; t_level; t_index } =
  let priority = function
    | Tvar -> 3 | Tproduct _ -> 2 | Tconstr _ | Tvec _ -> 3
    | Tarrow _ -> 1 | Tlink _ -> prio in
  let prio_current = priority t_desc in
  if prio_current < prio then fprintf ff "(";
  begin match t_desc with
  | Tvar ->
      (* prefix non generalized type variables with "_" *)
      let p = if t_level <> Misc.notgeneric then "" else "_" in
      fprintf ff "@['%s%s@]" p (type_name#name t_index)
  | Tproduct [] ->
     (* this situation should not happen after typing *)
     fprintf ff "ERROR"
  | Tproduct(ty_list) -> print_list (print (prio_current + 1)) " *" ff ty_list
  | Tconstr(name, ty_list, _) ->
     let n = List.length ty_list in
      if n = 1 then
	fprintf ff "@[%a@ %a@]" (print prio_current)
		(List.hd ty_list) print_qualid name
      else if n > 1
      then fprintf ff "@[(%a)@ %a@]" (print_list (print 0) ",") ty_list
		   print_qualid name 
      else fprintf ff "@[%a@]" print_qualid name
  | Tarrow { ty_kind; ty_name_opt; ty_arg; ty_res } ->
     let print_arg ff ty =
       match ty_name_opt with
       | None -> print (prio_current + 1) ff ty
       | Some(n) -> fprintf ff "(%s:%a)" (Ident.name n) (print 0) ty in
     fprintf ff "@[<hov 2>%a@ %s@ %a@]"
       print_arg ty_arg (arrow_tostring ty_kind)
       (print prio_current) ty_res
  | Tvec(ty, si) ->
     fprintf ff "@[%a[%a]@]" (print prio_current) ty print_size si
  | Tlink(link) -> print prio ff link
  end;
  if prio_current < prio then fprintf ff ")"  

let print_scheme ff { typ_body } = print 0 ff typ_body     

let print_type_params ff pl =
  print_list_r_empty (fun ff s -> fprintf ff "'%s" s) "("","") " ff pl

let print_size_params ff pl =
  print_list_r_empty (fun ff s -> fprintf ff "'%s" s) "["",""] " ff pl

let print_one_type_variable ff i =
  fprintf ff "'%s" (type_name#name i)

(* printing type declarations *)
let print_type_name ff (tc,ta) = match ta with
  | [] -> print_qualid ff tc
  | [i] -> fprintf ff "%a %a" print_one_type_variable i print_qualid tc
  | l -> fprintf ff "(%a)@ %a"
      (print_list print_one_type_variable ",") l
        print_qualid tc

(* prints one variant *)
let print_one_variant ff { qualid; info = constr_desc } =
  if constr_desc.constr_arity = 0
  then fprintf ff "@ |@[<3>@ %a@]" print_qualid qualid
  else fprintf ff "@ |@[<3>@ %a of@,%a@]"
      print_qualid qualid
      (print_list_l (print 1) "(" "* " ")") constr_desc.constr_arg


(* prints one label *)
let print_one_label ff { qualid; info = label_desc } =
  fprintf ff "@ @[<2>%a:@ %a@]"
    print_qualid qualid
    (print 0) label_desc.label_res

let print_type_desc ff = function
  | Abstract_type -> ()
  | Abbrev(_, ty) -> fprintf ff " = %a" (print 2) ty
  | Variant_type global_list ->
      fprintf ff " = %a"
        (print_list_r print_one_variant """""") global_list
  | Record_type global_list ->
      fprintf ff " = %a"
        (print_list_r print_one_label "{" ";" "}") global_list

let print_type_declaration ff { qualid; info = typ_desc } =
  type_name#reset;
  fprintf ff "%a @ %a"
    print_type_name (qualid, typ_desc.type_parameters)
    print_type_desc typ_desc.type_desc

let print_value_type_declaration ff { qualid; info = (is_const, ty_scheme) } =
  type_name#reset;
  let v = if is_const then "const" else "val" in
  fprintf ff "%s %a :@ %a" v print_qualid qualid print_scheme ty_scheme


(* the main printing functions *)
let output ff ty =
  fprintf ff "%a" (print 0) ty

let output_size ff si = print_size ff si

let output_type_declaration ff global_list =
  fprintf ff "@[<hov 2>%a@.@]"
    (print_list_l print_type_declaration "type ""and """)
    global_list

let output_value_type_declaration ff global_list =
  fprintf ff "@[<hov 2>%a@.@]"
    (print_list_l print_value_type_declaration """""")
    global_list




