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

(* print object code *)

open Misc
open Obc
open Format
open Pp_tools
module Printer = Printer.Make(Ptypinfo)
    
(* A qualified name [M.x] is print [x] when the current module is [M] *)
let longname ff ln =
  let ln = Initial.short (Modules.currentname ln) in
  match ln with
  | Lident.Name(m) -> Printer.shortname ff m
  | Lident.Modname(qual) -> Printer.qualident ff qual

let kind = function
  | Deftypes.Tfun _ -> "any"
  | Deftypes.Tnode(k) ->
     match k with
     | Deftypes.Tdiscrete -> "discrete"
     | Deftypes.Tcont -> "continuous"

(* Priorities *)
let priority_exp = function
  | Econst _ | Econstr0 _| Eglobal _ | Evar _ 
    | Estate _ | Earray_list _ | Eget _ | Eupdate _ | Eslice _
    | Econcat _ | Evec _ | Etranspose _ | Ereverse _ | Eflatten _
    | Erecord _ | Erecord_access _ | Erecord_with _
    | Etypeconstraint _ | Etuple _ | Efor _ | Ewhile _ -> 3
  | Econstr1 _ | Eapp _ | Esizeapp _ | Emethodcall _ | Eassert _ -> 2
  | Eassign _ | Eassign_state _  -> 1
  | Eifthenelse _  | Ematch _ | Elet _ | Eletvar _ | Eletmem _ | Eletinstance _
    | Eletsizefun _ | Esequence _ -> 0
  | Efun _ | Emachine _ -> 0

let p_internal_type ff ty =
  if !Misc.verbose then fprintf ff ": %a" Ptypes.output_type ty

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

let rec pattern ptype ff pat =
  let rec pattern ff pat = match pat with
    | Ewildpat -> fprintf ff "_"
    | Econstpat(i) -> immediate ff i
    | Econstr0pat(lname) -> longname ff lname
    | Econstr1pat(lname, pat_list) ->
       fprintf ff "@[%a%a@]"
         longname lname (print_list_r pattern "("","")") pat_list
    | Evarpat { id; ty } ->
       (* print the type in verbose mode only *)
       if !Misc.verbose then
         fprintf ff "@[(%a:%a)@]" Printer.name id ptype ty
       else Printer.name ff id
    | Etuplepat(pat_list) ->
       pattern_comma_list ptype ff pat_list
    | Ealiaspat(p, n) -> fprintf ff "@[%a as %a@]" pattern p Printer.name n
    | Eorpat(pat1, pat2) -> fprintf ff "@[%a | %a@]" pattern pat1 pattern pat2
    | Etypeconstraintpat(p, ty_exp) ->
       fprintf ff "@[(%a: %a)@]" pattern p Printer.ptype ty_exp
    | Erecordpat(n_pat_list) ->
       print_list_r
         (print_record longname pattern
            "" " =" "") "{" ";" "}" ff n_pat_list in
  pattern ff pat

and pattern_list ptype ff pat_list =
  print_list_r (pattern ptype) "" "" "" ff pat_list

and pattern_comma_list ptype ff pat_list =
  print_list_r (pattern ptype) "("","")" ff pat_list

let method_name m_name = m_name

(** Print the call to a method *)
let rec method_call ff { met_name = m; met_instance = i_opt; met_args = e_list } =
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
  | Eleft_record_access { label; arg } ->
     fprintf ff "@[%a.%a@]" left_value arg longname label
  | Eleft_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_value left (exp 0) idx

and print_self_name ff self_opt =
  match self_opt with
  | None -> Format.fprintf ff "self" | Some(id) -> Printer.name ff id

and left_state_value ff left =
  match left with
  | Eself_state(self_opt) -> print_self_name ff self_opt
  | Eleft_state_name { self; name } | Eleft_instance_name { self; name } ->
     Format.fprintf ff "%a.%a" print_self_name self Printer.name name
  | Eleft_state_record_access { label; arg } ->
     fprintf ff "@[%a.%a@]" left_state_value arg longname label
  | Eleft_state_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_state_value left (exp 0) idx
  | Eleft_state_primitive_access(left, a) ->
     fprintf ff "@[%a.%s@]" left_state_value left (state_primitive_access a)

and assign ff left e =
  match left with
  | Eleft_name(n) ->
     fprintf ff "@[<v 2>%a := %a@]" Printer.name n (exp 2) e
  | _ ->
     fprintf ff "@[<v 2>%a <- %a@]" left_value left (exp 2) e

and assign_state ff left e =
  match left with
  | Eself_state(self) -> 
     fprintf ff "@[<v 2>%a := %a@]" print_self_name self (exp 2) e
  | _ -> fprintf ff "@[<v 2>%a <- %a@]" left_state_value left (exp 2) e

and state_primitive_access a =
  match a with
  | Eder -> "der" | Epos -> "pos"
  | Ezero_out -> "zout"  | Ezero_in -> "zin" 

and var ff n = Printer.name ff n

and letvar ff n ty e_opt e =
  match e_opt with
  | None ->
     fprintf ff
       "@[<v 0>var %a%a in@ %a@]" Printer.name n p_internal_type ty (exp 0) e
  | Some(e0) ->
     fprintf ff "@[<v 0>var %a%a = %a in@ %a@]"
       Printer.name n p_internal_type ty (exp 0) e0 (exp 0) e

and exp prio ff e =
  let prio_e = priority_exp e in
  if prio_e < prio then fprintf ff "(";
  begin match e with
  | Econst(i) -> immediate ff i
  | Econstr0 { lname } -> longname ff lname
  | Econstr1 { lname; arg_list } ->
     fprintf ff "@[%a%a@]"
       longname lname (print_list_r (exp prio_e) "("","")") arg_list
  | Eglobal { lname } -> longname ff lname
  | Evar { id } -> var ff id
  | Estate(l) -> left_state_value ff l
  | Etuple(e_list) ->
     Pp_tools.print_tuple (exp prio_e) ff e_list
  | Eapp { f; arg_list } ->
     fprintf ff "@[<hov2>%a %a@]"
       (exp (prio_e + 1)) f (print_list_r (exp (prio_e + 1)) """""")
       arg_list
  | Esizeapp { f; size_list } ->
     fprintf ff "@[<hov2>%a<<%a>>@]"
       (exp (prio_e + 1)) f (print_list_r (exp (prio_e + 1)) "" "," "")
       size_list
  | Emethodcall m -> method_call ff m
  | Erecord(label_e_list) ->
     print_list_r
       (print_record
          longname (exp 0) "" " =" "") "{" ";" "}" ff label_e_list
  | Erecord_access { label; arg } ->
     fprintf ff "%a.%a" (exp prio_e) arg longname label
  | Erecord_with(e_record, label_e_list) ->
     fprintf ff "@[{ %a with %a }@]"
       (exp prio_e) e_record
       (print_list_r
          (print_record longname (exp 0) "" " =" "") "{" ";" "}") label_e_list
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
  | Eletsizefun(is_rec, sizefun_list, e) ->
     fprintf ff "@[<v0>let %s%a in@ %a@]"
       (if is_rec then "rec " else "")
       (print_list_r sizefun "" "and" "") sizefun_list
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
     fprintf ff "%a^%a" (exp prio_e) e (exp 3) size
  | Eslice { e; left; right } ->
     fprintf ff "%a{%a..%a}"
       (exp prio_e) e (exp 0) left (exp 0) right
  | Econcat { left; left_size; right; right_size } ->
     fprintf ff "{%a:%a | %a:%a}"
       (exp 0) left (exp 0) left_size (exp 0) right (exp 0) right_size
  | Earray_list(e_list) ->
     fprintf ff "[|%a|]"
       (Pp_tools.print_list_r (exp 0) "" ";" "") e_list
  | Etranspose { e; size_1; size_2 } ->
     fprintf ff "@[<hov2>transpose@,<<%a,%a>>@,(%a)@]"
       (exp 0) size_1 (exp 0) size_2 (exp 0) e
  | Ereverse { e; size } ->
     fprintf ff "@[<hov2>reverse@,<<%a>>@,(%a)@]" (exp 0) size (exp 0) e
  | Eflatten { e; size_1; size_2 } ->
      fprintf ff "@[<hov2>flatten@,<<%a,%a>>@,(%a)@]"
       (exp 0) size_1 (exp 0) size_2 (exp 0) e
  | Emachine(ma) -> machine ff ma
  | Efun { pat_list; e } ->
     fprintf ff
       "@[<hov2>(fun@ %a ->@ %a)@]"
       (pattern_list Printer.ptype) pat_list (exp 0) e
  end;
  if prio_e < prio then fprintf ff ")"

and sizefun ff { sf_id; sf_id_list; sf_e } =
  (* [id<<...>> = e] *)
  fprintf ff
    "@[%a%a =@ %a@]" var sf_id
    (print_list_r var "<<" "," ">>") sf_id_list (exp 0) sf_e

and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" (pattern Printer.ptype) p (exp 0) e

and exp_with_typ ff (e, ty) =
  fprintf ff "(%a%a)" (exp 2) e p_internal_type ty

and expression ff e = exp 0 ff e

and match_handler ff { m_pat = pat; m_body = b } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" (pattern Printer.ptype) pat (exp 0) b

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
    | None -> "" | Some(k) -> (Ptypes.mkind k) ^ " " in
  fprintf ff "%s%a%a%a = %a" (mem m_kind) Printer.name m_name
    (print_list_no_space (print_with_braces (exp 0) "[" "]") "" "" "")
    m_size p_internal_type m_typ (print_opt (exp 0)) m_value

and instance ff { i_name; i_machine; i_kind; i_params; i_size } =
  fprintf ff
    "@[%s %a@ %a%a%a@]" 
    (kind i_kind) Printer.name i_name (exp 0) i_machine
    (print_list_no_space
       (print_with_braces (exp 0) "(" ")") "" "" "")
    i_params
    (print_list_no_space
       (print_with_braces (exp 0) "[" "]") "" "" "")
    i_size

and pmethod ff { me_name; me_params; me_body; me_typ } =
  fprintf ff "@[<hov 2>method %s %a@ =@ (%a%a)@]"
    (method_name me_name) (pattern_list Printer.ptype) me_params (exp 2) me_body
    p_internal_type me_typ

and pinitialize ff i_opt =
  match i_opt with
  | None -> ()
  | Some(e) -> fprintf ff "@[<hov2>initialize@;%a@]" (exp 0) e

(* Print a machine *)
and machine ff { ma_name; ma_kind; ma_params; ma_initialize;
		 ma_memories; ma_instances; ma_methods; ma_assertion } =
  fprintf ff
    "@[<hov 2>%s machine@ %a@ (%a)@ \
     {@, %a@,@[<v2>memories@ @[%a@]@]@;@[<v 2>instances@ @[%a@]@]@;@[%a@]%a}@]"
    (kind ma_kind) Ident.fprint_t ma_name  
    (pattern_list Printer.ptype) ma_params
    pinitialize ma_initialize
    (print_list_r_empty memory """;""") ma_memories
    (print_list_r_empty instance """;""") ma_instances
    (print_list_r pmethod """""") ma_methods
    (print_opt machine) ma_assertion

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
let implementation ff impl = 
  let print_n_list ff n_list =
    Pp_tools.print_list_r Printer.shortname "(" "," ")" ff n_list in
  match impl with
  | Eletdef(n_list_e_list) ->
     let print ff (n_list, e) =
       fprintf ff "@[<hov2>%a =@ %a@]" print_n_list n_list (exp 0) e in
     fprintf ff "@[<v 0>let %a@.@]"
       (Pp_tools.print_list_l print "" "and " "") n_list_e_list
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
