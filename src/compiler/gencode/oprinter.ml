(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* print object code *)

open Misc
open Obc
open Format
open Pp_tools
module Printer = Printer.Make(Typinfo)
    
let kind = function
  | Deftypes.Tfun _ -> "any"
  | Deftypes.Tnode(k) ->
     match k with
     | Deftypes.Tdiscrete -> "discrete"
     | Deftypes.Tcont -> "continuous"

(* Priorities *)
let priority_exp = function
  | Econst _ | Econstr0 _| Eglobal _ | Evar _ 
    | Estate_access _ | Eget _ | Eupdate _ | Eslice _
    | Econcat _ | Evec _ | Erecord _ | Erecord_access _ | Erecord_with _
  | Etypeconstraint _ | Etuple _ | Efor _ | Ewhile _ -> 3
  | Econstr1 _ | Eapp _ | Emethodcall _ | Eassert _ -> 2
  | Eassign _ | Eassign_state _  -> 1
  | Eifthenelse _  | Ematch _ | Elet _ | Eletvar _ | Eletmem _ | Eletinstance _
    | Esequence _ -> 0
  | Efun _ | Emachine _ -> 0

let ptype ff ty = Ptypes.output_type ff ty

let immediate ff = function
  | Eint i ->
     if i < 0 then fprintf ff "(%a)" pp_print_int i else pp_print_int ff i
  | Eint32 i ->
     if i < 0
     then fprintf ff "(%al)" pp_print_int i
     else fprintf ff "%al"   pp_print_int i
  | Efloat f ->
     if f < 0.0 then fprintf ff "(%a)" pp_print_float f
     else pp_print_float ff f
  | Ebool b -> if b then fprintf ff "true" else fprintf ff "false"
  | Estring s -> fprintf ff "%S" s
  | Echar c -> fprintf ff "'%c'" c
  | Evoid -> pp_print_string ff "()"
  | Eany -> fprintf ff "any"

let print_record print1 print2 po sep pf ff { label; arg } =
  fprintf ff "@[<hov>%s@[%a@]%s@ @[%a@]%s@]" po print1 label sep print2 arg pf

let rec pattern ff pat = match pat with
  | Ewildpat -> fprintf ff "_"
  | Econstpat(i) -> immediate ff i
  | Econstr0pat(lname) -> Printer.longname ff lname
  | Econstr1pat(lname, pat_list) ->
     fprintf ff "@[%a%a@]"
       Printer.longname lname (print_list_r pattern "("","")") pat_list
  | Evarpat { id; ty } ->
     fprintf ff "@[(%a:%a)@]" Printer.name id Printer.ptype ty
  | Etuplepat(pat_list) ->
     pattern_comma_list ff pat_list
  | Ealiaspat(p, n) -> fprintf ff "@[%a as %a@]" pattern p Printer.name n
  | Eorpat(pat1, pat2) -> fprintf ff "@[%a | %a@]" pattern pat1 pattern pat2
  | Etypeconstraintpat(p, ty_exp) ->
     fprintf ff "@[(%a: %a)@]" pattern p Printer.ptype ty_exp
  | Erecordpat(n_pat_list) ->
     print_list_r
       (print_record Printer.longname pattern
          "" " =" "") "{" ";" "}" ff n_pat_list

and pattern_list ff pat_list =
  print_list_r pattern "" "" "" ff pat_list

and pattern_comma_list ff pat_list =
  print_list_r pattern "("","")" ff pat_list

and method_name m_name = m_name

(** Print the call to a method *)
and method_call ff { met_name = m; met_instance = i_opt; met_args = e_list } =
  let m = method_name m in
  let instance ff i_opt =
    match i_opt with
    | None -> (* a call to the self machine *) fprintf ff "self"
    | Some(o, e_list) ->
       match e_list with
       | [] -> fprintf ff "self.%a" Printer.name o
       | e_list ->
	  fprintf ff "self.%a.%a" Printer.name o
	    (print_list_no_space
	       (print_with_braces (exp 3) "(" ")") "" "." "") e_list in
  fprintf ff "@[<hov 2>%a.%s @ %a@]"
    instance i_opt m
    (print_list_r (exp 3) "" "" "") e_list

and left_value ff left =
  match left with
  | Eleft_name(n) -> Printer.name ff n
  | Eleft_record_access(left, n) ->
     fprintf ff "@[%a.%a@]" left_value left Printer.longname n
  | Eleft_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_value left (exp 0) idx

and left_state_value ff left =
  match left with
  | Eself -> fprintf ff "self."
  | Eleft_instance_name(n) -> Printer.name ff n
  | Eleft_state_global(ln) -> Printer.longname ff ln
  | Eleft_state_name(n) -> Printer.name ff n
  | Eleft_state_record_access(left, n) ->
     fprintf ff "@[%a.%a@]" left_state_value left Printer.longname n
  | Eleft_state_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_state_value left (exp 0) idx
  | Eleft_state_primitive_access(left, a) ->
     fprintf ff "@[%a%s@]" left_state_value left (state_primitive_access a)

and assign ff left e =
  match left with
  | Eleft_name(n) ->
     fprintf ff "@[<v 2>%a := %a@]" Printer.name n (exp 2) e
  | _ ->
     fprintf ff "@[<v 2>%a <- %a@]" left_value left (exp 2) e

and assign_state ff left e =
  match left with
  | Eleft_state_global(gname) ->
     fprintf ff "@[<v 2>%a := %a@]" Printer.longname gname (exp 2) e
  | _ -> fprintf ff "@[<v 2>%a <- %a@]" left_state_value left (exp 2) e

and state_primitive_access a =
  match a with
  | Eder -> ".der" | Epos -> ".pos"
  | Ezero_out -> ".zout"  | Ezero_in -> ".zin" 

and var ff n = Printer.name ff n

and letvar ff n ty e_opt e =
  match e_opt with
  | None ->
     fprintf ff
       "@[<v 0>var %a: %a in@ %a@]" Printer.name n ptype ty (exp 0) e
  | Some(e0) ->
     fprintf ff "@[<v 0>var %a: %a = %a in@ %a@]"
       Printer.name n ptype ty (exp 0) e0 (exp 0) e

and exp prio ff e =
  let prio_e = priority_exp e in
  if prio_e < prio then fprintf ff "(";
  begin match e with
  | Econst(i) -> immediate ff i
  | Econstr0 { lname } -> Printer.longname ff lname
  | Econstr1 { lname; arg_list } ->
     fprintf ff "@[%a%a@]"
       Printer.longname lname (print_list_r (exp prio_e) "("","")") arg_list
  | Eglobal { lname } -> Printer.longname ff lname
  | Evar { id } -> var ff id
  | Estate_access(l) -> left_state_value ff l
  | Etuple(e_list) ->
     fprintf ff "@[<hov2>%a@]" (print_list_r (exp prio_e) "("","")") e_list
  | Eapp { f; arg_list } ->
     fprintf ff "@[<hov2>%a %a@]"
       (exp (prio_e + 1)) f (print_list_r (exp (prio_e + 1)) """""")
       arg_list
  | Emethodcall m -> method_call ff m
  | Erecord(label_e_list) ->
     print_list_r
       (print_record
          Printer.longname (exp 0) "" " =" "") "{" ";" "}" ff label_e_list
  | Erecord_access { label; arg } ->
     fprintf ff "%a.%a" (exp prio_e) arg Printer.longname label
  | Erecord_with(e_record, label_e_list) ->
     fprintf ff "@[{ %a with %a }@]"
       (exp prio_e) e_record
       (print_list_r
          (print_record Printer.longname (exp 0) "" " =" "") "{" ";" "}") label_e_list
  | Etypeconstraint(e, ty_e) ->
     fprintf ff "@[(%a : %a)@]" (exp prio_e) e Printer.ptype ty_e
  | Eifthenelse(e, e1, e2) ->
     fprintf ff "@[<hv>if %a@ @[<hv 2>then@ %a@]@ @[<hv 2>else@ %a@]@]"
       (exp 0) e (exp 1) e1 (exp 1) e2
  | Elet(p, e1, e2) ->
     fprintf ff "@[<v 0>let %a in@ %a@]" pat_exp (p, e1) (exp (prio_e - 1)) e2
  | Eletvar { id; is_mutable; ty; e_opt; e } ->
     letvar ff id ty e_opt e
  | Eletmem(m_list, e) ->
     fprintf ff "@[<v 0>let @[<v 2>mem@,@[%a@]@] in@ %a@]"
       (print_list_r memory "" ";" "") m_list
       (exp 0) e
  | Eletinstance(i_list, e) ->
     fprintf ff "@[<v 0>let @[<v 2>instances@,@[%a@]@] in@ %a@]"
       (print_list_r instance "" ";" "") i_list
       (exp 0) e
  | Ematch(e, match_handler_l) ->
     fprintf ff "@[<v2>match %a with@ @[%a@]@]"
       (exp 0) e
       (print_list_l match_handler """""") match_handler_l
  | Efor { index; dir; left; right; e } ->
     fprintf ff "@[<hv>for %a = %a %s %a@ @[<hv 2>do@ %a@ done@]@]"
       Printer.name index (exp 0) left (if dir then "to" else "downto")
       (exp 0) right (exp 0) e
  | Ewhile { cond; e } ->
     fprintf ff "@[<hv>while %a do %a done@]@]"
       (exp 0) cond (exp 0) e
  | Eassert(e) ->
     fprintf ff "@[<hv>assert@ %a@]" (exp 2) e
  | Eassign(left, e) -> assign ff left e
  | Eassign_state(left, e) -> assign_state ff left e
  | Esequence(e_list) ->
     if e_list = []
     then fprintf ff "()"
     else
       fprintf ff
         "@[<hv>%a@]" (print_list_r (exp 1) "" ";" "") e_list
  | Eget { e; index } ->
     fprintf ff "%a.(@[%a@])" (exp prio_e) e (exp 0) index
  | Eupdate { e; size; index; arg } ->
     fprintf ff "@[<hov2>{%a:%a with@ %a = %a}@]"
       (exp prio_e) e (exp 0) size (exp 0) index (exp 0) arg
  | Evec { e; size } ->
     fprintf ff "%a[%a]" (exp prio_e) e (exp 0) size
  | Eslice { e; left; right } ->
     fprintf ff "%a{%a..%a}"
       (exp prio_e) e (exp 0) left (exp 0) right
  | Econcat { left; left_size; right; right_size } ->
     fprintf ff "{%a:%a | %a:%a}"
       (exp 0) left (exp 0) left_size (exp 0) right (exp 0) right_size
  | Emachine(ma) -> machine ff ma
  | Efun { pat_list; e } ->
     fprintf ff
       "@[<hov2>(fun@ %a ->@ %a)@]" pattern_list pat_list (exp 0) e
  end;
  if prio_e < prio then fprintf ff ")"

and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" pattern p (exp 0) e

and exp_with_typ ff (e, ty) =
  fprintf ff "(%a:%a)" (exp 2) e ptype ty

and expression ff e = exp 0 ff e

and match_handler ff { m_pat = pat; m_body = b } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" pattern pat (exp 0) b

and mkind mk =
  match mk with
  | None -> ""
  | Some(mk) ->
     match mk with
     | Econt -> "cont "
     | Ezero -> "zero "
     | Ehorizon -> "horizon "
     | Emajor -> "major "
     | Eencore -> "encore "
     | Eperiod -> "period "

and memory ff { m_name; m_value; m_typ; m_kind; m_size } =
  let mem = function
    | None -> "" | Some(k) -> (Ptypes.kind k) ^ " " in
  fprintf ff "%s%a%a : %a = %a" (mem m_kind) Printer.name m_name
    (print_list_no_space (print_with_braces (exp 0) "[" "]") "" "" "")
    m_size ptype m_typ (print_opt (exp 0)) m_value

and instance ff { i_name; i_machine; i_kind; i_params; i_size } =
  fprintf ff
    "@[%a : %s(%a)%a%a@]" Printer.name i_name (kind i_kind) (exp 0) i_machine
    (print_list_no_space
       (print_with_braces (exp 0) "(" ")") "" "" "")
    i_params
    (print_list_no_space
       (print_with_braces (exp 0) "[" "]") "" "" "")
    i_size

and pmethod ff { me_name; me_params; me_body; me_typ } =
  fprintf ff "@[<hov 2>method %s %a@ =@ (%a:%a)@]"
    (method_name me_name) pattern_list me_params (exp 2) me_body
    ptype me_typ

and pinitialize ff i_opt =
  match i_opt with
  | None -> ()
  | Some(e) -> fprintf ff "@[<hov2>initialize@;%a@]" (exp 0) e

(* Print a machine *)
and machine ff { ma_name; ma_kind; ma_params; ma_initialize;
		 ma_memories; ma_instances; ma_methods } =
  fprintf ff
    "@[<hov 2>machine(%s)(%a)%a@ \
     {@, %a@,@[<v2>memories@ @[%a@]@]@;@[<v 2>instances@ @[%a@]@]@;@[%a@]@]]}@.@]"
    (kind ma_kind) Ident.fprint_t ma_name 
    pattern_list ma_params
    pinitialize ma_initialize
    (print_list_r_empty memory """;""") ma_memories
    (print_list_r_empty instance """;""") ma_instances
    (print_list_r pmethod """""") ma_methods

let print_type_params ff pl =
      print_list_r_empty (fun ff s -> fprintf ff "'%s" s) "("","") " ff pl
    
let constr_decl ff c_decl =
      match c_decl with
      | Econstr0decl(n) -> fprintf ff "%s" n
      | Econstr1decl(n, ty_list) ->
         fprintf ff
           "@[%s of %a@]" n (print_list_l Printer.ptype "(" "* " ")") ty_list

let type_decl ff ty_decl =
  match ty_decl with
  | Eabstract_type -> ()
  | Eabbrev(ty) ->
     fprintf ff "%a" Printer.ptype ty
  | Evariant_type(constr_decl_list) ->
     fprintf
       ff "%a" (print_list_l constr_decl "" "|" "") constr_decl_list
  | Erecord_type(mut_n_ty_list) ->
     let print ff (is_mutable, n, ty) =
       fprintf ff "@[%s%a: %a@]" (if is_mutable then "mutable " else "")
         Printer.shortname n Printer.ptype ty in
     fprintf ff "%a"
       (print_list_r print "{" ";" "}") mut_n_ty_list

(* The main entry functions for expressions and instructions *)
let implementation ff impl = match impl with
  | Eletdef(n_e_list) ->
     let print ff (n, e) =
       fprintf ff "@[%a = %a@]" Printer.shortname n (exp 0) e in
     fprintf ff "@[<v 2>let %a@.@]"
       (Pp_tools.print_list_l print "" "and " "") n_e_list
  | Eopen(s) ->
     fprintf ff "@[open %s@.@]" s
  | Etypedecl(l) ->
     let print ff (s, s_list, ty_decl) =
       fprintf ff "%a%s =@ %a" print_type_params s_list
         s type_decl ty_decl in
     fprintf ff "@[<hov2>%a@.@]" (print_list_l print "type ""and """) l

let implementation_list ff impl_list =
  fprintf ff "@[(* %s *)@.@]" Misc.header_in_file;
  fprintf ff "@[open Ztypes@.@]";
  List.iter (implementation ff) impl_list

let program ff { p_impl_list } =
  implementation_list ff p_impl_list
