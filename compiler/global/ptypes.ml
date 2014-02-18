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
(* Printing a type expression *)

open Format
open Pp_tools
open Misc
open Lident
open Global
open Modules
open Deftypes

(* the long name of an ident is printed       *)
(* if it is different from the current module *)
let print_qualid ff qualid = 
  Lident.fprint_t ff (Initial.short (currentname (Modname(qualid))))

(* type variables are printed 'a, 'b,... *)
let type_name = new name_assoc_table int_to_alpha

(* generic printing of a list *)
let print_list print_el sep ff l =
  let rec printrec ff l =
    match l with
      [] -> ()
    | [x] -> print_el ff x
    | x::l -> fprintf ff "%a%s@ %a" print_el x sep printrec l
  in
    printrec ff l

let arrow_tostring = function 
  | Tany -> "-A->" | Tcont -> "-C->" 
  | Tdiscrete(s) -> if s then "-D->" else "-AD->" 

let rec print priority ff ty = match ty.t_desc with
  | Tvar -> fprintf ff "@['%s@]" (type_name#name ty.t_index)
  | Tproduct [] -> fprintf ff "ERROR"
  | Tproduct(ty_list) ->
      (if priority >= 2 then fprintf ff "@[(%a)@]" else fprintf ff "@[%a@]")
        (print_list (print 2) " *") ty_list
  | Tconstr(name, ty_list,_) ->
      let n = List.length ty_list in
        (if n = 1 then fprintf ff "@[%a@ %a@]" (print 2) (List.hd ty_list)
         else if n > 1
         then fprintf ff "@[(%a)@ %a@]" (print_list (print 2) ",") ty_list
         else fprintf ff "@[%a@]")
          print_qualid name
  | Tlink(link) -> print priority ff link

let print_scheme ff { typ_body = typ_body } =
  let print_arg_list ff = function
    | [] -> fprintf ff "unit"
    | ty_arg_list -> 
        fprintf ff "@[%a@]" (print_list_r (print 2) """ *""") ty_arg_list in
  match typ_body with
    | Tvalue(ty) -> print 0 ff ty
    | Tsignature(k, s, ty_arg_list, ty_res) ->
        fprintf ff "@[%a %s %a@]" 
          print_arg_list ty_arg_list
          (arrow_tostring k) (print 0) ty_res
      

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
let print_one_variant ff { qualid = qualid; info = constr_desc } =
  fprintf ff "@ |@[<3>@ %a@]" print_qualid qualid


(* prints one label *)
let print_one_label ff { qualid = qualid; info = label_desc } =
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
        (print_record print_one_label) global_list

let print_type_declaration ff { qualid = qualid; info = typ_desc } =
  type_name#reset;
  fprintf ff "%a @ %a"
    print_type_name (qualid, typ_desc.type_parameters)
    print_type_desc typ_desc.type_desc

let print_value_type_declaration ff { qualid = qualid; info = ty_scheme } =
  type_name#reset;
  fprintf ff "%a :@ %a" print_qualid qualid print_scheme ty_scheme


(* the main printing functions *)

let output ff ty =
  fprintf ff "%a" (print 0) ty

let output_type_declaration ff global_list =
  fprintf ff "@[<v>%a@.@]"
    (print_list_lb print_type_declaration "type ""and """)
    global_list

let output_value_type_declaration ff global_list =
  fprintf ff "@[<v>%a@.@]"
    (print_list_lb print_value_type_declaration "val ""val """)
    global_list




