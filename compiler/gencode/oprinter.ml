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
(* print object code *)

open Misc
open Location
open Ident
open Obc
open Format
open Pp_tools
       
(** Flag to print a machine as a collection of OCaml functions *)
(* A better solution is to add an extra printer *)
			    
let print_as_functions = ref false

(** Priorities *)
let rec priority_exp = function
  | Oconst _ | Oconstr0 _| Oglobal _ | Olocal _ | Ovar _ | Ostate _ | Oindex _
  | Orecord _ | Orecord_access _ | Otypeconstraint _ | Otuple _ -> 3
  | Oconstr1 _ | Oapp _ | Omethodcall _ | Ovec _ -> 2
  | Oifthenelse _  -> 1

and priority_inst = function
  | Olet _
  | Oletvar _ -> 1
  | Ofor _ | Owhile _ -> 3
  | Omatch _ -> 0
  | Oif _ -> 0
  | Oassign _ -> 2
  | Oassign_state _ -> 2
  | Osequence _ -> 1
  | Oexp(e) -> priority_exp e

(* Infix chars are surrounded by parenthesis *)
let is_infix =
  let module StrSet = Set.Make(String) in
  let set_infix =
    List.fold_right
      StrSet.add
      ["or"; "quo"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
      StrSet.empty in
  fun s -> StrSet.mem s set_infix

let parenthesis s =
  let c = String.get s 0 in
  if is_infix s then "(" ^ s ^ ")"
  else match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' -> s
    | '*' -> "( " ^ s ^ " )"
    | _ -> if s = "()" then s else "(" ^ s ^ ")"

let shortname ff s = fprintf ff "%s" (parenthesis s)

let longname ff ln =
  let ln = Initial.short(Modules.currentname ln) in
  match ln with
  | Lident.Name(s) -> shortname ff s
  | Lident.Modname({ Lident.qual = m; Lident.id = s }) ->
      fprintf ff "%s.%s" m (parenthesis s)

let name ff n = shortname ff (Ident.name n)

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
  | Oany ->
     fprintf ff "%s" (if !print_as_functions then "Obj.magic ()" else "any")
	     
let kind = function
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete _ -> "discrete"
  | Deftypes.Tcont -> "continuous"

let constructor_for_kind = function
  | Deftypes.Tcont -> "Hybrid" | Deftypes.Tdiscrete(true) -> "Node"
  | _ -> assert false
		
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
    | Otypefun(opt_name, ty_arg, ty) ->
       let arg prio ff (opt_name, ty) =
	 match opt_name with
	 | None -> ptype prio ff ty
	 | Some(n) -> fprintf ff "@[(%a : %a)@]" name n (ptype 0) ty in
       fprintf ff "@[<hov2>%a ->@ %a@]"
	       (arg prio_ty) (opt_name, ty_arg) (ptype prio_ty) ty
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

let ptype ff ty =
  let ty = if !print_as_functions then Types.remove_dependences ty else ty in
  Ptypes.output ff ty
      
let rec pattern ff pat = match pat with
  | Owildpat -> fprintf ff "_"
  | Oconstpat(i) -> immediate ff i
  | Oconstr0pat(lname) -> longname ff lname
  | Oconstr1pat(lname, pat_list) ->
      fprintf ff "@[%a%a@]"
        longname lname (print_list_r pattern "("","")") pat_list
  | Ovarpat(n, ty) ->
     fprintf ff "@[(%a:%a)@]" name n ptype ty
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

and method_name m_name =
  match m_name with
  | Ostep -> "step" | Oreset -> "reset" | Oderivatives -> "derivatives"
  | Ocrossings -> "crossings" | Omaxsize -> "maxsize"
  | Oreinit -> "reinit" | Ocin -> "cin" | Ocout -> "cout"
  | Ozin -> "zin" | Oclear_zin -> "clear_zin" | Ozout -> "zout" | Odout -> "dout"
  | Odzero -> "dzero"
  | Ocsize -> "csize" | Ozsize -> "zsize"
  | Ohorizon -> "horizon"

(** Print the call to a method *)
and method_call ff { met_name = m; met_instance = i_opt; met_args = e_list } =
  let m = method_name m in
  let instance_name ff i_opt =
    match i_opt with
    | None -> fprintf ff "self" | Some(o, _) -> name ff o in
  let instance ff i_opt =
    match i_opt with
    | None -> (* a call to the self machine *) fprintf ff "self"
    | Some(o, e_list) ->
       match e_list with
       | [] -> fprintf ff "self.%a" name o
       | e_list ->
	  fprintf ff "self.%a.%a" name o
		  (print_list_no_space
		     (print_with_braces (exp 3) "(" ")") "" "." "")
		  e_list in
  if !print_as_functions
  then fprintf ff "@[<hov 2>%a_%s %a@ %a@]"
	       instance_name i_opt m instance i_opt
	       (print_list_r (exp 3) "" "" "") e_list
  else fprintf ff "@[<hov 2>%a.%s @ %a@]"
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
  | Oleft_instance_name(n) ->
     if !print_as_functions then fprintf ff "self.%a" name n
     else name ff n
  | Oleft_state_global(ln) -> longname ff ln
  | Oleft_state_name(n) ->
     if !print_as_functions then fprintf ff "self.%a" name n
     else name ff n
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
  fprintf ff "@[<v 2>%a <- %a@]" left_state_value left (exp 2) e

and access ff a =
  let s =
    match a with
    | Oder -> "der" | Ocont -> "pos"
    | Ozero_out -> "zout"  | Ozero_in -> "zin" in
  fprintf ff "%s" s

and local ff n = name ff n

and var ff n =
  if !print_as_functions then fprintf ff "!%a" name n
  else name ff n

and letvar ff n ty e_opt i =
  match e_opt with
  | None ->
     if !print_as_functions
     then fprintf ff "@[<v 0>let %a = ref (Obj.magic (): %a) in@ %a@]"
		  name n ptype ty (inst 0) i
     else fprintf ff "@[<v 0>var %a: %a in@ %a@]"
                  name n ptype ty (inst 0) i
  | Some(e0) ->
     if !print_as_functions
     then fprintf ff "@[<v 0>let %a = ref (%a:%a) in@ %a@]"
		  name n (exp 0) e0 ptype ty (inst 0) i
     else fprintf ff "@[<v 0>var %a: %a = %a in@ %a@]"
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
  | Ovar(n) -> var ff n
  | Ostate(l) -> left_state_value ff l
  | Oindex(e, eidx) ->
      fprintf ff "%a.(@[%a@])" (exp prio_e) e (exp prio_e) eidx
  | Ovec(e, se) ->
     (* make a vector *)
     let print_vec ff e se =
       match e with
       | Oconst _ ->
	  fprintf ff "@[<hov 2>Array.make@ (%a)@ (%a)@]"
		  (exp prio_e) se (exp prio_e) e 
       | Ovec(e1, e2) ->
	  fprintf ff "@[<hov 2>Array.make_matrix@ (%a)@ (%a)@ (%a)@]"
		  (exp prio_e) se (exp prio_e) e2 (exp prio_e) e1
       | _ -> fprintf ff "@[<hov 2>Array.init@ @[(%a)@]@ @[(fun _ -> %a)@]@]"
		      (exp prio_e) se (exp prio_e) e in
     if !print_as_functions then print_vec ff e se
     else fprintf ff "%a[%a]" (exp prio_e) e (exp 0) se
  | Otuple(e_list) ->
      fprintf ff "@[<hov2>%a@]" (print_list_r (exp prio_e) "("","")") e_list
  | Oapp(e, e_list) ->
      fprintf ff "@[<hov2>%a %a@]"
        (exp (prio_e + 1)) e (print_list_r (exp (prio_e + 1)) """""") e_list
  | Omethodcall m -> method_call ff m
  | Orecord(r) ->
      print_record (print_couple longname (exp prio_e) """ =""") ff r
  | Orecord_access(e, lname) ->
      fprintf ff "%a.%a" (exp prio_e) e longname lname
  | Otypeconstraint(e, ty_e) ->
      fprintf ff "@[(%a : %a)@]" (exp prio_e) e print_concrete_type ty_e
  | Oifthenelse(e, e1, e2) ->
      fprintf ff "@[<hv>if %a@ @[<hv 2>then@ %a@]@ @[<hv 2>else@ %a@]@]"
        (exp 0) e (exp prio_e) e1 (exp prio_e) e2
  end;
  if prio_e < prio then fprintf ff ")"

and inst prio ff i =
  let prio_i = priority_inst i in
  if prio_i < prio then fprintf ff "(";
  begin
    match i with
    | Olet(p, e, i) ->
       fprintf ff "@[<v 0>let %a in@ %a@]" pat_exp (p, e) (inst (prio_i-1)) i
    | Oletvar(x, ty, e_opt, i) -> letvar ff x ty e_opt i
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
       else fprintf ff "@[<hv>%a@]" (print_list_r (inst prio_i) "" ";" "") i_list
    | Oexp(e) -> exp prio ff e
    | Oif(e, i) -> fprintf ff "@[<hov>if %a@ then@ %a@]" (exp 0) e (inst 1) i
  end;
  if prio_i < prio then fprintf ff ")"

and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" pattern p (exp 0) e

and exp_with_typ ff (e, ty) =
  fprintf ff "(%a:%a)" (exp 2) e ptype ty
	  
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

let print_memory ff { m_name = n; m_value = e_opt; m_typ = ty;
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

let print_name_with_type ff (n, ty) =
  fprintf ff "%a : %a" name n ptype ty

let print_instance ff { i_name = n; i_machine = ei; i_kind = k;
		      i_params = e_list; i_size = i_size } =
  fprintf ff "@[%a : %s(%a)%a@]" name n (kind k) (exp 0) ei
	  (print_list_no_space
	     (print_with_braces (exp 0) "[" "]") "" "" "")
	  i_size

let print_method ff { me_name = m_name; me_params = p_list; me_body = i } =
  fprintf ff "@[<hov 2>method %s %a =@ %a@]"
    (method_name m_name) pattern_list p_list (inst 0) i

(** Define the data-type for the internal state of a machine *)
let def_type_for_a_machine ff f memories instances =
  let one_entry ff (n, m) =
    fprintf ff "@[mutable %a : '%s@]" name n m in
  let i, params, entries =
    List.fold_right
      (fun { m_name = n } (i, params, entries) ->
        let m = Misc.int_to_alpha i in (i+1, m :: params, (n, m) :: entries))
      memories (0, [], []) in
  let i, params, entries =
    List.fold_right
      (fun { i_name = n } (i, params, entries) ->
        let m = Misc.int_to_alpha i in (i+1, m :: params, (n, m) :: entries))
      instances (i, params, entries) in
  (* if the state is empty, produce the dummy state type [unit] *)
  if entries = []
  then fprintf ff "@[type %s = unit@.@.@]" f
  else
      fprintf ff "@[<v 2>type @[%a@] %s =@ { @[%a@] }@.@.@]"
        (print_list_r (fun ff s -> fprintf ff "'%s" s) "("","")") params
        f
        (print_list_r one_entry """;""") entries

  
(** Define the method *)
let def_method_as_a_function f ff
    { me_name = me_name; me_params = pat_list; me_body = i } =
  fprintf ff "@[<v 2>let %s_%s self %a =@ %a in@]"
    f (method_name me_name) pattern_list pat_list (inst 0) i

(* create an array of type t[n_1]...[n_k] *)
let array_make print arg ff ie_size =
  let rec array_rec ff = function
    | [] -> fprintf ff "%a" print arg 
    | ie :: ie_size ->
       fprintf ff "@[<hov>Array.init %a@ (fun _ -> %a)@]"
	       (exp 3) ie array_rec ie_size in
  array_rec ff ie_size

let rec array_bool ff =
  function
  | [] -> fprintf ff "false"
  | [ie] -> fprintf ff "Array.make %a false" (exp 3) ie
  | ie :: ie_list ->
     fprintf ff
	     "@[<hov 2>Array.init %a@ (fun _ -> %a)@]" (exp 3) ie array_bool ie_list
     
let rec array_float ff =
  function
  | [] -> fprintf ff "1.0"
  | [ie] -> fprintf ff "Array.create_float %a" (exp 3) ie
  | ie :: ie_list ->
     fprintf ff
	     "@[<hov 2>Array.init %a@ (fun _ -> %a)@]"
	     (exp 3) ie array_float ie_list

(*
(** Represent a machine as a record of functions *)
(* order methods in this order: *)
(* alloc < maxsize < derivatives < step < crossings < reset *)
let order m1 m2 =
  let int { me_name = me_name } =
    match me_name with
    | Omaxsize -> 1 | Oderivatives -> 2
    | Ostep -> 3 | Ocrossings -> 4 | Oreset -> 5
    | Ocin -> 6 | Ocout -> 7 | Odout -> 8
    | Ozin -> 9 | Ozout -> 10 | _ -> 0 in
  Pervasives.compare (int m1) (int m2)
 *)
	     
(** Define the allocation function *)
let def_alloc_as_a_function f memories ff instances =
  let print_memory ff { m_name = n; m_value = e_opt;
			m_typ = ty; m_kind = k_opt; m_size = m_size } =
    match k_opt with
    | None ->
       begin
	 match e_opt with
         | None -> fprintf ff "@[%a = %a@]"
			   name n
			   (array_make
			      (fun ff _ -> fprintf ff "(Obj.magic (): %a)"
						   ptype ty) ())
			   m_size
         | Some(e) ->
	    fprintf ff "@[%a = %a@]"
		    name n
		    (array_make exp_with_typ (e, ty)) m_size
       end
    | Some(m) ->
       match m with
       | Deftypes.Zero ->
	  fprintf ff "@[%a = @[<hov 2>{ zin = %a;@ zout = %a }@]@]"
		  name n array_bool m_size array_float m_size
       | Deftypes.Cont ->
	  fprintf ff "@[%a = @[<hov 2>{ pos = %a; der = %a }@]@]"
		  name n array_float m_size array_float m_size
       | Deftypes.Horizon | Deftypes.Period ->
			     fprintf ff "%a = %a" name n array_float m_size
       | Deftypes.Encore -> fprintf ff "%a = %a" name n array_bool m_size in

  let print_instance ff { i_name = n; i_machine = ei;
			i_kind = k; i_params = e_list; i_size = ie_size } =
    fprintf ff "@[%a = %a (* %s *)@ @]" name n
	    (array_make (fun ff n -> fprintf ff "%a_alloc ()" name n) n)
	    ie_size (kind k)  in
  if memories = []
  then if instances = []
       then fprintf ff "@[let %s_alloc _ = () in@]" f
       else
         fprintf ff "@[<v 2>let %s_alloc _ =@ %a in@]"
                 f (print_record print_instance) instances
  else if instances = []
  then
    fprintf ff "@[<v 2>let %s_alloc _ =@ %a in@]"
            f (print_record print_memory) memories
  else
    fprintf ff "@[<v 2>let %s_alloc _ =@ { @[%a@,%a@] } in@]"
            f
            (print_list_r print_memory """;"";") memories
            (print_list_r print_instance """;""") instances

(* print an entry [let n_alloc, n_step, n_reset, ... = f ... in] *)
(* for every instance *)
let def_instance_function m_list ff { i_name = n; i_machine = ei; i_kind = k;
				      i_params = e_list; i_size = ie_size } =
  (** Define the method *)
  let method_name ff { me_name = me_name } =
    let m = method_name me_name in
    fprintf ff "%s = %a_%s" m name n m in

  let list_of_methods ff m_list =  print_list_r method_name """;""" ff m_list in

  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany -> () | Deftypes.Tdiscrete(false)
  | _ -> let k = constructor_for_kind k in
	 fprintf ff "@[let %s { alloc = %a_alloc; %a } = %a %a in@]"
		 k name n list_of_methods m_list
		 (exp 0) ei (print_list_r (exp 1) "" " " "") e_list
	  
(** Print a machine *)
let machine_as_a_class ff f { ma_kind = k;
                              ma_params = pat_list;
			      ma_memories = memories;
                              ma_instances = instances;
                              ma_methods = m_list } =
  fprintf ff
  "@[<hov 2>let %s = machine(%s)%a@ \
    {@, @[@[<v 2>memories@ @[%a@]@]@;@[<v 2>instances@ @[%a@]@]@;@[%a@]@]]}@.@]"
    f
    (kind k)
    pattern_list pat_list
    (print_list_r_empty print_memory """;""") memories
    (print_list_r_empty print_instance """;""") instances
    (print_list_r print_method """""") m_list


(** Print a machine as pieces with a type definition for the state *)
(** and a collection of functions *)
(* The general form is:
 * type ('a1, ...) f = { ... }
 * let f x1 ... xn =
 *   let { alloc = o1_alloc; step = o1_step; reset = o1_reset, ... } = f1 ... in
 *   ...
 *   let { alloc = om_alloc; step = om_step; reset = om_reset, ... } = fm ... in
 *   let f_alloc () = ... in
 *   let f_step y = ... in
 *   let f_reset = ... in
 *   { alloc = f_alloc; step = f_step; reset = f_reset, ... } *)	     
let machine_as_functions ff f { ma_kind = k;
                                ma_params = pat_list;
				ma_memories = memories;
                                ma_instances = instances;
                                ma_methods = m_list } =
  (* print either [(f)] *)
  (* or [k { alloc = f_alloc; m1 = f_m1; ...; mn = f_mn }] *)
  let tuple_of_methods ff m_list =
    match k with
    | Deftypes.Tstatic _ | Deftypes.Tany -> fprintf ff "%s" f
    | Deftypes.Tdiscrete _
    | Deftypes.Tcont ->
       let method_name ff { me_name = me_name } =
	 let m = method_name me_name in
	 fprintf ff "@[%s = %s_%s@]" m f m in
       let k = constructor_for_kind k in
       fprintf ff "@[%s { alloc = %s_alloc; %a }@]"
	       k f (print_list_r method_name "" ";" "") m_list in
		  
  (* print the type for [f] *)
  def_type_for_a_machine ff f memories instances;
  (* print the code for [f] *)
  fprintf ff "@[<hov 2>let %s %a = @ @[%a@]@ @[%a@]@ @[%a@]@ %a@.@.@]"
	  f pattern_list pat_list
	  (print_list_r (def_instance_function m_list) "" "" "") instances
	  (def_alloc_as_a_function f memories) instances
	  (print_list_r (def_method_as_a_function f) """""") m_list
	  tuple_of_methods m_list

let machine ff f m =
  if !print_as_functions then machine_as_functions ff f m
  else machine_as_a_class ff f m


let implementation ff impl = match impl with
  | Oletvalue(n, i) ->
      fprintf ff "@[<v 2>let %a = %a@.@.@]" shortname n (inst 0) i
  | Oletfun(n, pat_list, i) ->
      fprintf ff "@[<v 2>let %a %a =@ %a@.@.@]"
        shortname n pattern_list pat_list (inst 0) i
  | Oletmachine(n, m) -> machine ff n m
  | Oopen(s) ->
      fprintf ff "@[open %s@.@]" s
  | Otypedecl(l) ->
      fprintf ff "@[%a@.@]"
        (print_list_l
            (fun ff (s, s_list, ty_decl) ->
                  fprintf ff "%a%s =@ %a"
                    print_type_params s_list
                    s type_decl ty_decl)
            "type ""and """)
        l

let implementation_list ff as_functions impl_list =
  print_as_functions := as_functions;
  fprintf ff "@[(* %s *)@.@]" header_in_file;
  fprintf ff "@[open Ztypes@.@]";
  List.iter (implementation ff) impl_list
