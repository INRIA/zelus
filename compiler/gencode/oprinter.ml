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

(* print object code *)

open Misc
open Location
open Ident
open Obc
open Format
open Pp_tools
open Printer
       
(** Priorities *)
let rec priority_exp = function
  | Oconst _ | Oconstr0 _| Oglobal _ | Olocal _ | Ovar _ | Ostate _ | Oaccess _
  | Orecord _ | Orecord_access _ | Orecord_with _
  | Otypeconstraint _ | Otuple _ -> 3
  | Oconstr1 _ | Oapp _ | Omethodcall _
    | Ovec _ | Oupdate _ | Oslice _ | Oconcat _ -> 2
  | Oifthenelse _  -> 0 | Oinst i -> priority_inst i

and priority_inst = function
  | Olet _
  | Oletvar _ -> 0
  | Ofor _ | Owhile _ -> 3
  | Omatch _ -> 0
  | Oif _ -> 0
  | Oassign _ -> 2
  | Oassign_state _ -> 2
  | Osequence _ -> 0
  | Oexp(e) -> priority_exp e

let kind = function
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete _ -> "discrete"
  | Deftypes.Tcont -> "continuous" | Deftypes.Tproba -> "proba"

let rec psize prio ff si =
  let operator = function Splus -> "+" | Sminus -> "-" in
  let priority = function Splus -> 0 | Sminus -> 1 in
  match si with
  | Sconst(i) -> fprintf ff "%d" i
  | Sglobal(ln) -> longname ff ln
  | Sname(n) -> name ff n
  | Sop(op, e1, e2) ->
     let prio_op = priority op in
     if prio > prio_op then fprintf ff "(";
     fprintf ff "@[%a %s %a@]"
	     (psize prio_op) e1 (operator op) (psize prio_op) e2;
     if prio > prio_op then fprintf ff ")"

let print_concrete_type ff ty =
  let priority =
    function | Otypevar _ | Otypeconstr _ | Otypevec _ -> 2
             | Otypetuple _ -> 2 | Otypefun _ -> 1 in
  let rec ptype prio ff ty =
    let prio_ty = priority ty in
    if prio_ty < prio then fprintf ff "(";
    begin match ty with
    | Otypevar(s) -> fprintf ff "'%s" s
    | Otypefun(k, opt_name, ty_arg, ty) ->
       let arg prio ff (opt_name, ty) =
	 match opt_name with
	 | None -> ptype prio ff ty
	 | Some(n) -> fprintf ff "@[(%a : %a)@]" name n (ptype 0) ty in
       let k = match k with Ofun -> "->" | Onode -> "=>" in
       fprintf ff "@[<hov2>%a %s@ %a@]"
	       (arg prio_ty) (opt_name, ty_arg) k (ptype prio_ty) ty
    | Otypetuple(ty_list) ->
       fprintf ff
	       "@[<hov2>%a@]" (print_list_r (ptype prio_ty) "("" *"")") ty_list
    | Otypeconstr(ln, ty_list) ->
       fprintf ff "@[<hov2>%a@]%a"
               (print_list_r_empty (ptype 2) "("","")") ty_list longname ln
    | Otypevec(ty_arg, si) ->
       fprintf ff "@[%a[%a]@]" (ptype prio_ty) ty_arg (psize 0) si
    end;
    if prio_ty < prio then fprintf ff ")" in
  ptype 0 ff ty

let ptype ff ty = Ptypes.output ff ty
      
let immediate ff = function
  | Oint i ->
     if i < 0 then fprintf ff "(%a)" pp_print_int i else pp_print_int ff i
  | Oint32 i ->
     if i < 0
     then fprintf ff "(%al)" pp_print_int i
     else fprintf ff "%al"   pp_print_int i
  | Ofloat f ->
     if f < 0.0 then fprintf ff "(%a)" pp_print_float f
     else pp_print_float ff f
  | Obool b -> if b then fprintf ff "true" else fprintf ff "false"
  | Ostring s -> fprintf ff "%S" s
  | Ochar c -> fprintf ff "'%c'" c
  | Ovoid -> pp_print_string ff "()"
  | Oany -> fprintf ff "any"
	     
let rec pattern ff pat = match pat with
  | Owildpat -> fprintf ff "_"
  | Oconstpat(i) -> immediate ff i
  | Oconstr0pat(lname) -> longname ff lname
  | Oconstr1pat(lname, pat_list) ->
     fprintf ff "@[%a%a@]"
             longname lname (print_list_r pattern "("","")") pat_list
  | Ovarpat(n, ty_exp) ->
     fprintf ff "@[(%a:%a)@]" name n print_concrete_type ty_exp
  | Otuplepat(pat_list) ->
     pattern_comma_list ff pat_list
  | Oaliaspat(p, n) -> fprintf ff "@[%a as %a@]" pattern p name n
  | Oorpat(pat1, pat2) -> fprintf ff "@[%a | %a@]" pattern pat1 pattern pat2
  | Otypeconstraintpat(p, ty_exp) ->
     fprintf ff "@[(%a: %a)@]" pattern p print_concrete_type ty_exp
  | Orecordpat(n_pat_list) ->
     print_record (print_couple longname pattern """ =""") ff n_pat_list
                  
and pattern_list ff pat_list =
  print_list_r pattern """""" ff pat_list
               
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
       | [] -> fprintf ff "self.%a" name o
       | e_list ->
	  fprintf ff "self.%a.%a" name o
		  (print_list_no_space
		     (print_with_braces (exp 3) "(" ")") "" "." "") e_list in
  fprintf ff "@[<hov 2>%a.%s @ %a@]"
	  instance i_opt m
	  (print_list_r (exp 3) "" "" "") e_list
          
and left_value ff left =
  match left with
  | Oleft_name(n) -> name ff n
  | Oleft_record_access(left, n) ->
     fprintf ff "@[%a.%a@]" left_value left longname n
  | Oleft_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_value left (exp 0) idx
             
and left_state_value ff left =
  match left with
  | Oself -> fprintf ff "self."
  | Oleft_instance_name(n) -> name ff n
  | Oleft_state_global(ln) -> longname ff ln
  | Oleft_state_name(n) -> name ff n
  | Oleft_state_record_access(left, n) ->
     fprintf ff "@[%a.%a@]" left_state_value left longname n
  | Oleft_state_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_state_value left (exp 0) idx
  | Oleft_state_primitive_access(left, a) ->
     fprintf ff "@[%a.%a@]" left_state_value left access a

and assign ff left e =
  match left with
  | Oleft_name(n) ->
     fprintf ff "@[<v 2>%a := %a@]" name n (exp 2) e
  | _ ->
     fprintf ff "@[<v 2>%a <- %a@]" left_value left (exp 2) e

and assign_state ff left e =
  match left with
  | Oleft_state_global(gname) ->
     fprintf ff "@[<v 2>%a := %a@]" longname gname (exp 2) e
  | _ -> fprintf ff "@[<v 2>%a <- %a@]" left_state_value left (exp 2) e

and access ff a =
  let s =
    match a with
    | Oder -> "der" | Ocont -> "pos"
    | Ozero_out -> "zout"  | Ozero_in -> "zin" in
  fprintf ff "%s" s

and local ff n = name ff n

and var ff n = name ff n

and letvar ff n ty e_opt i =
  match e_opt with
  | None ->
     fprintf ff "@[<v 0>var %a: %a in@ %a@]" name n ptype ty (inst 0) i
  | Some(e0) ->
     fprintf ff "@[<v 0>var %a: %a = %a in@ %a@]"
	     name n ptype ty (exp 0) e0 (inst 0) i

and exp prio ff e =
  let prio_e = priority_exp e in
  if prio_e < prio then fprintf ff "(";
  begin match e with
  | Oconst(i) -> immediate ff i
  | Oconstr0(lname) -> longname ff lname
  | Oconstr1(lname, e_list) ->
     fprintf ff "@[%a%a@]"
             longname lname (print_list_r (exp prio_e) "("","")") e_list
  | Oglobal(ln) -> longname ff ln
  | Olocal(n) -> local ff n
  | Ovar(_, n) -> local ff n
  | Ostate(l) -> left_state_value ff l
  | Oaccess(e, eidx) ->
     fprintf ff "%a.(@[%a@])" (exp prio_e) e (exp prio_e) eidx
  | Ovec(e, se) ->
     fprintf ff "%a[%a]" (exp prio_e) e (psize 0) se
  | Oupdate(se, e1, i, e2) ->
     fprintf ff "@[<hov2>{%a:%a with@ %a = %a}@]"
             (exp prio_e) e1 (psize prio_e) se (exp 0) i (exp 0) e2
  | Oslice(e, s1, s2) ->
     fprintf ff "%a{%a..%a}"
             (exp prio_e) e (psize 0) s1 (psize 0) s2
  | Oconcat(e1, s1, e2, s2) ->
     fprintf ff "{%a:%a | %a:%a}"
             (exp 0) e1 (psize 0) s1 (exp 0) e2 (psize 0) s2
  | Otuple(e_list) ->
     fprintf ff "@[<hov2>%a@]" (print_list_r (exp prio_e) "("","")") e_list
  | Oapp(e, e_list) ->
     fprintf ff "@[<hov2>%a %a@]"
             (exp (prio_e + 1)) e (print_list_r (exp (prio_e + 1)) """""")
             e_list
  | Omethodcall m -> method_call ff m
  | Orecord(r) ->
     print_record (print_couple longname (exp prio_e) """ =""") ff r
  | Orecord_access(e_record, lname) ->
     fprintf ff "%a.%a" (exp prio_e) e_record longname lname
  | Orecord_with(e_record, r) ->
     fprintf ff "@[{ %a with %a }@]"
	     (exp prio_e) e_record
	     (print_list_r
		(print_couple longname (exp prio_e) """ =""") "" ";" "") r
  | Otypeconstraint(e, ty_e) ->
     fprintf ff "@[(%a : %a)@]" (exp prio_e) e print_concrete_type ty_e
  | Oifthenelse(e, e1, e2) ->
     fprintf ff "@[<hv>if %a@ @[<hv 2>then@ %a@]@ @[<hv 2>else@ %a@]@]"
             (exp 0) e (exp 1) e1 (exp 1) e2
  | Oinst(i) -> inst prio ff i
  end;
  if prio_e < prio then fprintf ff ")"

and inst prio ff i =
  let prio_i = priority_inst i in
  if prio_i < prio then fprintf ff "(";
  begin
    match i with
    | Olet(p, e, i) ->
       fprintf ff "@[<v 0>let %a in@ %a@]" pat_exp (p, e) (inst (prio_i-1)) i
    | Oletvar(x, _, ty, e_opt, i) -> letvar ff x ty e_opt i
    | Omatch(e, match_handler_l) ->
       fprintf ff "@[<v2>match %a with@ @[%a@]@]"
	       (exp 0) e
	       (print_list_l match_handler """""") match_handler_l
    | Ofor(is_to, n, e1, e2, i3) ->
       fprintf ff "@[<hv>for %a = %a %s %a@ @[<hv 2>do@ %a@ done@]@]"
	       name n (exp 0) e1 (if is_to then "to" else "downto")
	       (exp 0) e2 (inst 0) i3
    | Owhile(e1, i2) ->
       fprintf ff "@[<hv>while %a do %a done@]@]"
	       (exp 0) e1 (inst 0) i2
    | Oassign(left, e) -> assign ff left e
    | Oassign_state(left, e) -> assign_state ff left e
    | Osequence(i_list) ->
       if i_list = []
       then fprintf ff "()"
       else
         fprintf ff
                 "@[<hv>%a@]" (print_list_r (inst 1) "" ";" "") i_list
    | Oexp(e) -> exp prio ff e
    | Oif(e, i1, None) ->
       fprintf ff "@[<hov>if %a@ then@ %a@]" (exp 0) e sinst i1
    | Oif(e, i1, Some(i2)) ->
       fprintf ff "@[<hov>if %a@ then@ %a@ else %a@]"
	       (exp 0) e sinst i1 sinst i2
  end;
  if prio_i < prio then fprintf ff ")"

(* special treatment to add an extra parenthesis if [i] is a sequence *)
and sinst ff i =
  match i with
  | Osequence(i_list) ->
     if i_list = [] then fprintf ff "()"
     else fprintf ff
                  "@[<hv>%a@]" (print_list_r (inst 1) "(" ";" ")") i_list
  | _ -> inst 0 ff i
  
and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" pattern p (exp 0) e
          
and exp_with_typ ff (e, ty) =
  fprintf ff "(%a:%a)" (exp 2) e ptype ty
	  
and expression ff e = exp 0 ff e

and match_handler ff { w_pat = pat; w_body = b } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" pattern pat (inst 0) b
          
(** The main entry functions for expressions and instructions *)
let rec type_decl ff = function
  | Oabstract_type -> ()
  | Oabbrev(ty) -> print_concrete_type ff ty
  | Ovariant_type(constr_decl_list) ->
     print_list_l constr_decl """| """ ff constr_decl_list
  | Orecord_type(s_ty_list) ->
     print_record
       (print_couple pp_print_string print_concrete_type """ :""") ff s_ty_list
       
and constr_decl ff = function
  | Oconstr0decl(s) -> fprintf ff "%s" s
  | Oconstr1decl(s, ty_list) ->
     fprintf ff "%s of %a" s (print_list_l print_concrete_type """ *""") ty_list
             
let memory ff { m_name = n; m_value = e_opt; m_typ = ty;
		m_kind = k_opt; m_size = m_size } =
  let mem = function
    | None -> ""
    | Some(k) -> (Printer.kind k) ^ " " in
  match e_opt with
  | None -> fprintf ff "%s%a%a : %a"
		    (mem k_opt) name n
		    (print_list_no_space (print_with_braces (exp 0)
							    "[" "]") "" "" "")
		    m_size ptype ty
  | Some(e) ->
     fprintf ff "%s%a%a : %a = %a" (mem k_opt) name n
	     (print_list_no_space (print_with_braces (exp 0) "[" "]") "" "" "")
	     m_size ptype ty (exp 0) e
             
let instance ff { i_name = n; i_machine = ei; i_kind = k;
		  i_params = e_list; i_size = i_size } =
  fprintf ff "@[%a : %s(%a)%a%a@]" name n (kind k) (exp 0) ei
	  (print_list_no_space
	     (print_with_braces (exp 0) "(" ")") "" "" "")
	  e_list
	  (print_list_no_space
	     (print_with_braces (exp 0) "[" "]") "" "" "")
	  i_size
          
let pmethod ff
            { me_name = m_name; me_params = p_list; me_body = i; me_typ = ty } =
  fprintf ff "@[<hov 2>method %s %a@ =@ (%a:%a)@]"
          (method_name m_name) pattern_list p_list (inst 2) i ptype ty
          
let pinitialize ff i_opt =
  match i_opt with
  | None -> ()
  | Some(e) -> fprintf ff "@[<hov2>initialize@;%a@]" (inst 0) e
		       
(** Print a machine *)
let machine f ff { ma_kind = k; ma_params = pat_list; ma_initialize = i_opt;
		   ma_memories = memories; ma_instances = instances;
                   ma_methods = m_list } =
  fprintf ff
   "@[<hov 2>let %s = machine(%s)%a@ \
   {@, %a@,@[<v2>memories@ @[%a@]@]@;@[<v 2>instances@ @[%a@]@]@;@[%a@]@]]}@.@]"
   f
   (kind k)
   pattern_list pat_list
   pinitialize i_opt
   (print_list_r_empty memory """;""") memories
   (print_list_r_empty instance """;""") instances
   (print_list_r pmethod """""") m_list

let implementation ff impl = match impl with
  | Oletvalue(n, i) ->
     fprintf ff "@[<v 2>let %a = %a@.@.@]" shortname n (inst 0) i
  | Oletfun(n, pat_list, i) ->
     fprintf ff "@[<v 2>let %a %a =@ %a@.@.@]"
             shortname n pattern_list pat_list (inst 0) i
  | Oletmachine(n, m) -> machine n ff m
  | Oopen(s) ->
     fprintf ff "@[open %s@.@]" s
  | Otypedecl(l) ->
     fprintf ff "@[%a@.@]"
             (print_list_l
                (fun ff (s, s_list, ty_decl) ->
                  fprintf ff "%a%s =@ %a"
                    Ptypes.print_type_params s_list
                    s type_decl ty_decl)
            "type ""and """)
        l

let implementation_list ff impl_list =
  fprintf ff "@[(* %s *)@.@]" header_in_file;
  fprintf ff "@[open Ztypes@.@]";
  List.iter (implementation ff) impl_list
