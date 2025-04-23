(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
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

let mkind k =
  match k with
  | Cont -> "cont" | Zero -> "zero"
  | Period -> "period" | Horizon -> "horizon"
  | Encore -> "encore" | Major -> "major"

let vkind = function Tconst -> "const " | Tstatic -> "static " | Tany -> "any"
let tkind = function Tdiscrete -> "discrete" | Tcont -> "hybrid"

let kind k = match k with | Tfun(v) -> vkind v | Tnode(t) -> tkind t

let arrow_tostring = function 
  | Tfun(k) ->
     (match k with Tconst -> "-V->" | Tstatic -> "-S->" | Tany -> "-A->")
  | Tnode(k) ->
     (match k with Tdiscrete -> "-D->" | Tcont -> "-C->")
    
(* Print a size expression *)
let rec size prio ff si =
  let open Defsizes in
  let operator = function Splus -> "+" | Sminus -> "-" | Smult -> "*" in
  let p_operator = function Splus -> 0 | Sminus -> 1 | Smult -> 3 in
  let priority si =
    match si with
    | Svar _ | Sint _ -> 3 | Sfrac _ -> 2 | Sop(op, _, _) -> p_operator op in
  let prio_s = priority si in
  if prio > prio_s then fprintf ff "(";
  begin match si with
  | Svar(x) -> fprintf ff "%s" (Ident.name x)
  | Sint(i) -> fprintf ff "%d" i
  | Sfrac { num; denom } ->
     fprintf ff "@[%a/%d@]" (size prio_s) num denom
  | Sop(op, si1, si2) ->
     fprintf ff "@[%a %s %a@]"
       (size prio_s) si1 (operator op) (size prio_s) si2;
  end;
  if prio > prio_s then fprintf ff ")"

(* Print a size constraint *)
let constraints_t ff sc =
  let open Defsizes in
  let priority =
    function
    | App _ -> 3 | Fix _ -> 2 | Rel _ -> 2 | And _ -> 1 | Let _ -> 0
    | If _ -> 0 | Forall _ -> 2 | True | False -> 2 | Loc _ ->2 in
  let eq_t ff { rel; lhs; rhs } =
    let s = match rel with | Eq -> "=" | Lt -> "<" | Lte -> "<=" in
    fprintf ff "@[(%a %s %a)@]" (size 0) lhs s (size 0) rhs in
  let def_t ff (id, e) =
    fprintf ff "@[<hov 2>%s =@ %a@]" (Ident.name id) (size 0) e in
  let rec fix_def_t ff (id, id_list, c) =
    fprintf ff "@[<hov 2>%s %a@ =@ %a@]" (Ident.name id)
      (Pp_tools.print_list_r Ident.fprint_t "(" "," ")") id_list
      (constraint_t 0) c
  and constraint_t prio ff sc =
    let prio_current = priority sc in
    if prio_current < prio then fprintf ff "(";
    begin match sc with
    | Rel(eq) -> eq_t ff eq
    | And(c_list) ->
       Pp_tools.print_list_r (constraint_t prio_current) "" " &&" "" ff c_list
    | Let(id_e_list, sc) ->
       fprintf ff
         "@[<hov0>%a@ %a@]"
         (Pp_tools.print_list_r def_t "let " " and" " in") id_e_list
         (constraint_t 0) sc
    | App(f, e_list) ->
       fprintf ff "@[<hov2>%a@ %a@]" Ident.fprint_t f
         (Pp_tools.print_list_r (size 0) "(" "," ")") e_list
    | Fix(f_id_list_c_list, c) ->
       (* [let rec f1(n1,...) = c1 and ... fk(n1,...) = ck in c] *)
       fprintf ff "@[<hov0>%a@ %a@]"
         (Pp_tools.print_list_r fix_def_t "let rec " " and" " in")
         f_id_list_c_list
         (constraint_t 0) c
    | If(sc1, sc2, sc3) ->
       fprintf ff "@[<hov0>if %a@ then@ %a@ else@ %a@]"
         (constraint_t 0) sc1 (constraint_t 0) sc2 (constraint_t 0) sc3
    | Forall(id, e, sc) ->
       fprintf ff "@[<hov0>forall@ %s@ lt %a@ do %a done@]"
          (Ident.name id) (size 0) e (constraint_t 0) sc
    | True -> fprintf ff "true"
    | False -> fprintf ff "false"
    | Loc(loc, sc) -> constraint_t prio ff sc
    end;
  if prio_current < prio then fprintf ff ")" in
  constraint_t 0 ff sc
     
let rec print prio ff { t_desc; t_level; t_index } =
  let print_constraints id_list ff sc =
    let open Defsizes in
    match sc with
    | True -> ()
    | _ -> if !Misc.print_types_with_size_constraints then
             fprintf ff "@[<hov2>with@ %a@]" constraints_t sc
           else print_list_r (fun ff id -> fprintf ff "?%a" Ident.fprint_t id)
                  "with " "," "" ff id_list in
  let priority = function
    | Tvar -> 3 | Tproduct _ -> 2 | Tconstr _ | Tvec _ -> 3
    | Tarrow _ | Tsizefun _ -> 1 | Tlink _ -> prio in
  let prio_current = priority t_desc in
  if prio_current < prio then fprintf ff "(";
  begin match t_desc with
  | Tvar ->
      (* prefix non generalized type variables with "_" *)
      let p = if t_level <> Misc.notgeneric then "" else "_" in
      fprintf ff "@['%s%s@]" p (type_name#name t_index)
  | Tproduct [] ->
     (* this situation should not happen after typing *)
     fprintf ff "?"
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
     fprintf ff "@[[%a]%a@]" (size 0) si (print prio_current) ty 
  | Tsizefun { id_list; ty; constraints } ->
     if Defsizes.constraint_is_true constraints then
       fprintf ff "@[<v2>%a.%a@]"
         (print_list_r Ident.fprint_t "<<" "," ">>") id_list
         (print prio_current) ty
     else fprintf ff "@[<v2>%a.%a@ %a@]"
         (print_list_r Ident.fprint_t "<<" "," ">>") id_list
         (print prio_current) ty (print_constraints id_list) constraints
  | Tlink(link) -> print prio ff link
  end;
  if prio_current < prio then fprintf ff ")"  

let print_scheme ff { typ_body } = print 0 ff typ_body     

let print_type_params ff pl =
  print_list_r_empty (fun ff s -> fprintf ff "'%s" s) "("","") " ff pl

let size_params ff pl =
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
  let v = if is_const then "val const" else "val" in
  fprintf ff "%s %a :@ %a" v print_qualid qualid print_scheme ty_scheme


(* the main printing functions *)
let output_type ff ty =
  fprintf ff "@[%a@]" (print 0) ty

let output_size ff si = size 0 ff si

let output_tentry ff { t_path; t_sort; t_tys } = 
  let vkind = function Tconst -> "c" | Tstatic -> "s" | Tany -> "a" in
  let tkind = function Tdiscrete -> "d" | Tcont -> "h" in
  let kind k = match k with | Tfun(v) -> vkind v | Tnode(t) -> tkind t in
  let init pref i =
    match i with | No -> "" | Eq | Decl _ -> pref ^ "/" in
  let rec path ff p = match p with
    | Pkind(k) -> fprintf ff "%s" (kind k)
    | Pon(p, k) -> fprintf ff "@[<hov 2>%a on@ %s@]" path p (kind k)
    | Psize -> fprintf ff "size" in  
  let sort ff t_sort = match t_sort with
    | Sort_val -> fprintf ff "val/"
    | Sort_var -> fprintf ff "var/"
    | Sort_mem { m_mkind = mk; m_last; m_init; m_default } ->
       fprintf ff "@[<hov2>%s%s%s%s@]"
         ((match mk with | None -> "mem" | Some(mk) -> mkind mk) ^ "/")
         (if m_last then "l/" else "")
         (init "i" m_init)
         (init "d" m_default) in
  fprintf ff "@[<hov2>%a/%a%a@]"
    path t_path sort t_sort print_scheme t_tys

let output_type_declaration ff global_list =
  fprintf ff "@[<hov 2>%a@.@]"
    (print_list_l print_type_declaration "type ""and """)
    global_list

let output_value_type_declaration ff global_list =
  fprintf ff "@[<hov 2>%a@.@]"
    (print_list_l print_value_type_declaration """""")
    global_list




