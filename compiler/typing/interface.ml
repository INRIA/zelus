(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2023 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* read an interface *)

open Location
open Lident
open Zelus
open Global
open Deftypes
open Modules
open Types
open Format

(* types of errors *)
type error =
  | Eunbound_type_constr of Lident.t
  | Eunbound_global_value of Lident.t
  | Etype_constr_arity of Lident.t * int * int
  | Eunbound_type_var of string
  | Eunbound_size_var of string
  | Erepeated_type_param of string
  | Erepeated_constructor of string
  | Erepeated_label of string
  | Ealready_defined_type of string
  | Ealready_defined_constr of string
  | Ealready_defined_label of string
  | Ealready_defined_value of string
  | Ecyclic_abbreviation
      
exception Error of Location.t * error
				
let error loc e = raise(Error(loc, e))
		       
(* printing error messages *)
let message loc kind =
  begin
    match kind with
    | Eunbound_type_constr(longname) ->
       eprintf "%aType error: The type constructor %s is unbound.@."
	 output_location loc (modname longname)
    | Eunbound_global_value(longname) ->
       eprintf "%aType error: The global value %s is unbound.@."
	 output_location loc (modname longname)
    | Etype_constr_arity(longname, arit, arit') ->
       eprintf "%aType error: The type constructor %s expects %d argument(s),@ \
                but is here given %d argument(s).@."
         output_location loc
         (modname longname) arit arit'
    | Eunbound_type_var(n) ->
       eprintf "%aType error: The type variable %s is unbound.@."
         output_location loc
         n
    | Eunbound_size_var(n) ->
       eprintf "%aType error: The size type variable %s is unbound.@."
         output_location loc
         n
    | Erepeated_type_param(n) ->
       eprintf "%aType error: Repeated parameter in type declaration.@."
         output_location loc
    | Erepeated_constructor(n) ->
       eprintf "%aType error: Two constructors are named %s@."
         output_location loc n
    | Erepeated_label(n) ->
       eprintf "%aType error: Two labels are named %s@."
         output_location loc n
    | Ealready_defined_type(n) ->
        eprintf
          "%aType error: The type %s already exists in the current module.@."
          output_location loc n
    | Ealready_defined_constr(n) ->
       eprintf
         "%aType error: The constructor %s already exists in \
          the current module.@."
         output_location loc n
    | Ealready_defined_label(n) ->
        eprintf
          "%aType error: The label %s already exists in the current module.@."
          output_location loc n
    | Ealready_defined_value(n) ->
        eprintf
          "%aType error: The value %s already exists in the current module.@."
          output_location loc n
    | Ecyclic_abbreviation ->
       eprintf "%aType error: This definition is cyclic.@."
         output_location loc
  end;
  raise Misc.Error

let make desc = { desc = desc; loc = no_location }
		  
(* type checking of type declarations *)
let global n desc = { qualid = Modules.qualify n; info = desc }
		      
let rec free_of_type (size_vars, typ_vars) ty =
  match ty.desc with
  | Etypevar(x) ->
     size_vars, if List.mem x typ_vars then typ_vars else x :: typ_vars
  | Etypetuple(ty_list) ->
     List.fold_left free_of_type (size_vars, typ_vars) ty_list
  | Etypeconstr(_,ty_list) ->
     List.fold_left free_of_type (size_vars, typ_vars) ty_list
  | Etypefun(_, ty_arg, ty_res) ->
     free_of_type (free_of_type (size_vars, typ_vars) ty_arg) ty_res
  | Evec(ty, si) ->
     let size_vars, typ_vars = free_of_type (size_vars, typ_vars) ty in
     free_size_of_type size_vars si, typ_vars
  | Esize(_, si) -> free_size_of_type size_vars si, typ_vars

and free_size_of_type size_vars si =
  match si.desc with
  | Esizevar(x) -> if List.mem x size_vars then size_vars else x :: size_vars
  | Esizeconst _ -> size_vars
  | Esizeop(_, si1, si2) ->
     free_size_of_type (free_size_of_type size_vars si1) si2
					
(* checks that every type is defined *)
(* and used with the correct arity *)
let constr_name loc s arity =
  let { qualid = name; info = desc } =
    try
      Modules.find_type s
    with
      | Not_found -> error loc (Eunbound_type_constr(s)) in
  let arity' = List.length desc.type_parameters in
    if arity' <> arity
    then error loc (Etype_constr_arity(s, arity', arity));
  name

let skindtype = function | Kconst -> Tconst | Kstatic -> Tstatic | Kany -> Tany
let tkindtype = function | Kdiscrete -> Tdiscrete | Khybrid -> Thybrid
let kindtype = function
  | Kfun(k) -> Tfun(skindtype k) | Knode(k) -> Tnode(tkindtype k)

let skindoftype = function | Kconst -> Tconst | Kstatic -> Tstatic | Kany -> Tany
let tkindoftype = function | Tdiscrete -> Kdiscrete | Thybrid -> Khybrid
let skindoftype = function
  | Tconst -> Kconst | Tstatic -> Kstatic | Tany -> Kany
let kindoftype = function
  | Tfun(k) -> Kfun(skindoftype k) | Tnode(k) -> Knode(tkindoftype k)

let typ_of_type_expression size_vars typ_vars typ =
  let rec typrec typ =
    match typ.desc with
    | Etypevar(s) ->
       begin try
           List.assoc s typ_vars
         with
           Not_found -> error typ.loc (Eunbound_type_var(s))
       end
    | Etypetuple(l) ->
       Types.product (List.map typrec l)
    | Etypeconstr(s, ty_list) ->
       let name = constr_name typ.loc s (List.length ty_list) in
       Types.nconstr name (List.map typrec ty_list)
    | Etypefun(k, ty_arg, ty_res) ->
       Types.arrowtype (kindtype k) (typrec ty_arg) (typrec ty_res)
    | Esize(is_singleton, si) ->
       Types.size is_singleton (size si)
    | Evec(ty, si) ->
       Types.vec (typrec ty) (size si)
  and size si =
    match si.desc with
    | Esizevar(s) ->
       begin try
           List.assoc s size_vars
         with
           Not_found -> error typ.loc (Eunbound_size_var(s))
       end
    | Esizeconst(i) -> Types.const(i)
    | Esizeop(s_op, si1, si2) ->
       let o =
	 match s_op with
         | Esize_plus -> Deftypes.Splus | Esize_minus -> Deftypes.Sminus
         | Esize_mult -> Deftypes.Smult in
       Types.op o (size si1) (size si2) in
  typrec typ
	    
let rec type_expression_of_typ typ =
  match typ.t_desc with
  | Tvar -> make (Etypevar("'a" ^ (string_of_int typ.t_index)))
  | Tproduct(l) ->
     make (Etypetuple(List.map type_expression_of_typ l))
  | Tconstr(s, ty_list, _) ->
     make (Etypeconstr(Modules.currentname (Lident.Modname(s)),
                       List.map type_expression_of_typ ty_list))
  | Tarrow(k, ty_arg, ty_res) ->
     make (Etypefun(kindoftype k, type_expression_of_typ ty_arg,
		    type_expression_of_typ ty_res))
  | Tvec(ty, si) ->
     make (Evec(type_expression_of_typ ty, size_expression_of_size si))
  | Tsize(is_singleton, si) ->
     make (Esize(is_singleton, size_expression_of_size si))
  | Tlink(typ) -> type_expression_of_typ typ

and size_expression_of_size si =
  let operation =
    function
      Sminus -> Esize_minus | Splus -> Esize_plus | Smult -> Esize_mult in
  match si.t_desc with
  | Svar -> make (Esizevar("'n" ^ (string_of_int si.t_index)))
  | Sconst(v) -> make (Esizeconst(v))
  | Sop(op, si1, si2) ->
     make (Esizeop(operation op, size_expression_of_size si1,
                   size_expression_of_size si2))
  | Slink(si) -> size_expression_of_size si

(* translate the internal representation of a type into a type definition *)
let type_decl_of_type_desc tyname
    { type_desc; type_parameters } =
  (* variant types *)
  let variant_type
      { qualid = qualid; info = { constr_arg = arg_l; constr_arity = arit } } =
    let desc =
      if arit = 0 then
        Econstr0decl(Modules.shortname qualid)
      else Econstr1decl(Modules.shortname qualid,
                        List.map type_expression_of_typ arg_l) in
    make desc in
  (* record types *)
  let record_type { qualid = qualid; info = { label_arg = arg } } =
    Modules.shortname qualid, type_expression_of_typ arg in

  let params = List.map (fun i -> "'a" ^ (string_of_int i)) type_parameters in
  let type_decl_desc =
    match type_desc with
      | Abstract_type -> Eabstract_type
      | Variant_type(c_list) -> Evariant_type(List.map variant_type c_list)
      | Record_type(l_list) -> Erecord_type(List.map record_type l_list)
      | Abbrev(_, ty) -> Eabbrev(type_expression_of_typ ty) in
  (tyname, params, make type_decl_desc)


(* translating a declared type into an internal type *)
let scheme_of_type typ =
  let size_vars, typ_vars = free_of_type ([], []) typ in
  let size_vars = List.map (fun v -> (v, new_generic_size_var ())) size_vars in
  let typ_vars = List.map (fun v -> (v, new_generic_var ())) typ_vars in
  let typ = typ_of_type_expression size_vars typ_vars typ in
  { size_vars = List.map snd size_vars;
    typ_vars = List.map snd typ_vars;
    typ_body = typ }

(* analysing a type declaration *)
let check_no_repeated_type_param loc typ_params =
  let rec checkrec tp =
    match tp with
      | [] -> ()
      | x :: tp ->
          if List.mem x tp then error loc (Erepeated_type_param(x))
          else checkrec tp in
    checkrec typ_params

let check_no_repeated_constructor loc l =
  let rec checkrec cont l =
    match l with
      | [] -> ()
      | ({ desc = Econstr0decl(s) } | { desc = Econstr1decl(s, _) }) :: l ->
          if List.mem s cont  then error loc (Erepeated_constructor(s))
          else checkrec (s :: cont) l in
    checkrec [] l

let check_no_repeated_label loc l =
  let rec checkrec cont l =
    match l with
        [] -> ()
      | (s,_) :: l ->
          if List.mem s cont then error loc (Erepeated_label(s))
          else checkrec (s :: cont) l in
    checkrec [] l

(* typing type definitions *)
let type_variant_type size_vars typ_vars constr_decl_list final_typ =
  let type_one_variant { desc } =
    match desc with
    | Econstr0decl(s) ->
        global s { constr_arg = []; constr_res = final_typ; constr_arity = 0 }
    | Econstr1decl(s, te_list) ->
       let ty_list =
         List.map (typ_of_type_expression size_vars typ_vars) te_list in
        global s { constr_arg = ty_list; constr_res = final_typ;
                   constr_arity = List.length ty_list } in
  List.fold_left
    (fun l constr_decl -> (type_one_variant constr_decl) :: l)
    [] constr_decl_list

let type_record_type size_vars typ_vars label_type_list final_typ =
  let type_one_label (s, typ_expr) =
    let typ_arg = typ_of_type_expression size_vars typ_vars typ_expr in
    (global s { label_arg = final_typ; label_res = typ_arg }) in
    List.fold_left (fun l one_label -> (type_one_label one_label) :: l)
      [] label_type_list

(* first makes an initial type environnement *)
let make_initial_typ_environment loc typ_name typ_params =
    check_no_repeated_type_param loc typ_params;
    let typ_desc = { type_parameters = List.map (fun _ -> 0) typ_params;
                     type_desc = Abstract_type } in
    try
      add_type typ_name typ_desc;
      global typ_name typ_desc
    with
      | Already_defined(name) ->
          error loc (Ealready_defined_type name)

let type_one_typedecl loc gtype (typ_name, typ_params, size_params, typ) =
  let size_vars =
    List.map (fun v -> (v, new_generic_size_var ())) size_params in
  let typ_vars =
    List.map (fun v -> (v, new_generic_var ())) typ_params in
  let final_typ =
    Types.nconstr (Modules.qualify typ_name)
      (List.map (fun v -> List.assoc v typ_vars) typ_params) in

  let type_desc =
    match typ.desc with
    | Eabstract_type -> Abstract_type
    | Eabbrev(ty) ->
        Abbrev(List.map (fun (_, v) -> v) typ_vars,
               typ_of_type_expression size_vars typ_vars ty)
    | Evariant_type constr_decl_list ->
        check_no_repeated_constructor loc constr_decl_list;
        let l =
          type_variant_type size_vars typ_vars constr_decl_list final_typ in
        (* add the list of constructors to the symbol table *)
        begin try
            List.iter (fun g -> add_constr g.qualid.id g.info) l;
            Variant_type l
          with
          | Modules.Already_defined (name) ->
              error loc (Ealready_defined_constr name)
        end
    | Erecord_type label_decl_list ->
        check_no_repeated_label loc label_decl_list;
        let l = type_record_type size_vars typ_vars label_decl_list final_typ in
        (* add the list of record fields to the symbol table *)
        begin try
            List.iter (fun g -> add_label g.qualid.id g.info) l;
            Record_type l
          with
          | Modules.Already_defined (name) ->
              error loc (Ealready_defined_label name)
        end
  in

    (* modify the description associated to the declared type *)
    gtype.info.type_desc <- type_desc;
    gtype.info.type_parameters <-
      List.map (fun (_, ty) -> Deftypes.index ty) typ_vars;
    gtype

(* the main functions *)
let typedecl ff loc ty_name ty_params size_params typ =
  try
    let gtype = make_initial_typ_environment loc ty_name ty_params in
    let gtype =
      type_one_typedecl loc gtype (ty_name, ty_params, size_params, typ) in
    if !Misc.print_types then
      Ptypes.output_type_declaration ff [gtype]
  with
    | Error(loc, k) -> message loc k

(* analysing a value declaration *)
let add_type_of_value ff loc name is_const ty_scheme =
  try
    add_value name (value_desc is_const ty_scheme (Modules.qualify name));
    if !Misc.print_types then
      Ptypes.output_value_type_declaration ff [global name ty_scheme]
  with
    | Already_defined(x) -> message loc (Ealready_defined_value(x))

let update_type_of_value ff loc name is_const ty_scheme =
  try
    let info = Modules.find_value (Lident.Name(name)) in
    set_type info ty_scheme
  with
  | Not_found -> add_type_of_value ff loc name is_const ty_scheme
                                   
(* adding the type signature for a constant and a function. *)
(* [is_const = true] means that the identifier defines a compile-time value *)
let constdecl ff loc name is_const typ =
  add_type_of_value ff loc name is_const (scheme_of_type typ)

let fundecl ff loc name typ =
  add_type_of_value ff loc name true (scheme_of_type typ)

let interface ff inter =
  match inter.desc with
    | Einter_open(modname) -> Modules.open_module modname
    | Einter_typedecl { name; ty_params; size_params; ty_decl } ->
        typedecl ff inter.loc name ty_params size_params ty_decl
    | Einter_constdecl { name; const; ty; info } ->
        constdecl ff inter.loc name const ty

let interface_list ff p_list =
  try
    List.iter (interface ff) p_list
  with Error (loc, err) -> message loc err
 
