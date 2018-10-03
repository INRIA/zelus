(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2018                                               *)
(*                                                                        *)
(*  Marc Pouzet   Timothy Bourke                                          *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* the initial module *)

open Misc
open Lident
open Global
open Deftypes
open Modules

let pervasives_module = "Pervasives"
let pervasives_name id = { qual = pervasives_module;id = id }
let abstract_type params = 
  { type_desc = Abstract_type; type_parameters = params }
let abstract_type qualident arity =
  { qualid = qualident; info = abstract_type arity }
let abbrev_type params (ty_parameters, ty) = 
  { type_desc = Abbrev(ty_parameters, ty); type_parameters = params }
let abbrev_type qualident params (ty_parameters, ty) =
  { qualid = qualident; info = abbrev_type params (ty_parameters, ty)}
let value qualident tys =
  { qualid = qualident; info = value_desc false tys qualident }
  
let int_ident = pervasives_name "int"
let int32_ident = pervasives_name "int32"
let int64_ident = pervasives_name "int64"
let bool_ident = pervasives_name "bool"
let zero_ident = pervasives_name "zero"
let float_ident = pervasives_name "float"
let char_ident = pervasives_name "char"
let string_ident = pervasives_name "string"
let sig_ident = pervasives_name "signal"
let unit_ident = pervasives_name "unit"
let list_ident = pervasives_name "list"

let type_desc_int = abstract_type int_ident []
let type_desc_int32 = abstract_type int32_ident []
let type_desc_int64 = abstract_type int64_ident []
let type_desc_zero = abstract_type zero_ident []
let type_desc_bool = abstract_type bool_ident []
let type_desc_float = abstract_type float_ident []
let type_desc_char = abstract_type char_ident []
let type_desc_string = abstract_type string_ident []
let type_desc_unit = abstract_type unit_ident []
let type_desc_signal = abstract_type sig_ident [generic]
let type_desc_list = abstract_type list_ident [generic]

(* sum types. Not implemented in Zelus for the moment *)
let constr id ty_list = make (Tconstr(id, ty_list, ref Tnil))

(* the [array] type *)
let array_ident = pervasives_name "array"
let type_desc_array = abstract_type array_ident [generic]
let empty_array_ident = pervasives_name "[||]"

let typ_int = constr int_ident []
and typ_int32 = constr int32_ident []
and typ_int64 = constr int64_ident []
and typ_bool = constr bool_ident []
and typ_zero = constr zero_ident []
and typ_char = constr char_ident []
and typ_string = constr string_ident []
and typ_float = constr float_ident []
and typ_unit = constr unit_ident []
and typ_signal ty = constr sig_ident [ty]
and typ_array ty = constr array_ident [ty]
and typ_list ty = constr list_ident [ty]

(* global types loaded initially *)
let tglobal =
  [ type_desc_int;
    type_desc_int32;
    type_desc_int64;
    type_desc_bool;
    type_desc_zero;
    type_desc_float;
    type_desc_char;
    type_desc_string;
    type_desc_unit;
    type_desc_signal;
    type_desc_array;
    type_desc_list ]

(* global constructed values loaded initially *)
let cglobal = []

let nil_ident = pervasives_name "[]"
let cons_ident = pervasives_name "::"

let value_desc_nil =
  let ta = make Tvar in
  value nil_ident { typ_vars = [ta]; typ_body = typ_list ta }
    
let value_desc_cons =
  let ta = make Tvar in
  let ta_list = typ_list ta in
  value cons_ident
    { typ_vars = [ta];
      typ_body = make (Tfun(Tany, None, make (Tproduct [ta; ta_list]), ta_list))
    }
  
(* global values loaded initially *)
let vglobal =
  [ value_desc_nil;
    value_desc_cons ]

(* some names from the initial module can be used shortly *)
let short =
  let module StrSet = Set.Make(String) in
  let table = 
    List.fold_right 
      StrSet.add 
      ["int"; "int32"; "int64";
       "bool"; "zero"; "float"; "char"; "string"; "signal"; "unit";
       "array"; "[||]"; "list"; "[]"; "::"; "Some"; "None"]
      StrSet.empty in
  function
  | Modname({ qual = m; id = s }) as modname ->
      (* [Pervasives.s] is printed [s] when [s] is unbound *)
      if m = pervasives_module then if StrSet.mem s table then Name(s)
        else
          try let { qualid = { qual = m } } = Modules.find_value (Name(s)) in
              if m = pervasives_module then Name(s) else modname 
          with | Not_found -> modname
      else modname
  | Name _ as name -> name
  
let set_no_pervasives () = 
  default_used_modules := [];
  (* build the initial environment *)
  List.iter (fun x -> add_type x.qualid.id x.info) tglobal;
  List.iter (fun x -> add_constr x.qualid.id x.info) cglobal;
  List.iter (fun x -> add_value x.qualid.id x.info) vglobal
  

