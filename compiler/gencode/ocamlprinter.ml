(**************************************************************************)
(*                                                                        *)
(*                                Zelus                                   *)
(*               A synchronous language for hybrid systems                *)
(*                       http://zelus.di.ens.fr                           *)
(*                                                                        *)
(*                    Marc Pouzet and Timothy Bourke                      *)
(*                                                                        *)
(*  Copyright 2012 - 2019. All rights reserved.                           *)
(*                                                                        *)
(*  This file is distributed under the terms of the CeCILL-C licence      *)
(*                                                                        *)
(*  Zelus is developed in the INRIA PARKAS team.                          *)
(*                                                                        *)
(**************************************************************************)

(* print object code as OCaml functions *)

open Misc
open Location
open Ident
open Obc
open Format
open Pp_tools
open Printer
open Oprinter


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
  | Oany -> fprintf ff "Obj.magic ()"
		    
		    
let default_list_of_methods = [Oaux.step; Oaux.reset]

let constructor_for_kind = function
  | Deftypes.Tcont
  | Deftypes.Tdiscrete(true)
  | Deftypes.Tproba -> if !Misc.with_copy then "Cnode" else "Node"
  | _ -> assert false
let extra_methods m_list =
  if !Misc.with_copy then Oaux.copy :: m_list else m_list
let expected_list_of_methods = function
  | Deftypes.Tcont
  | Deftypes.Tdiscrete(true)
  | Deftypes.Tproba -> extra_methods default_list_of_methods
  | _ -> assert false
     
let print_concrete_type ff ty =
  let priority =
    function | Otypevar _ | Otypeconstr _ | Otypevec _ -> 2
             | Otypetuple _ -> 2 | Otypefun _ -> 1 in
  let rec ptype prio ff ty =
    let prio_ty = priority ty in
    if prio_ty < prio then fprintf ff "(";
    begin match ty with
    | Otypevar(s) -> fprintf ff "%s" s
    | Otypefun(k, _, ty_arg, ty) ->
        begin match k with
          | Ofun ->
              fprintf ff "@[<hov2>%a ->@ %a@]"
                (ptype (prio_ty+1)) ty_arg (ptype prio_ty) ty
          | Onode ->
              fprintf ff "@[<hov2>(%a, %a) node@]"
                (ptype (prio_ty+1)) ty_arg (ptype prio_ty) ty
        end
    | Otypetuple(ty_list) ->
       fprintf ff
	       "@[<hov2>%a@]" (print_list_r (ptype prio_ty) "("" *"")") ty_list
    | Otypeconstr(ln, ty_list) ->
       fprintf ff "@[<hov2>%a@]%a"
               (print_list_r_empty (ptype 2) "("","")") ty_list longname ln
    | Otypevec(ty_arg, _) ->
       fprintf ff "@[%a %a@]" (ptype prio_ty) ty_arg
               longname (Lident.Modname Initial.array_ident)
    end;
    if prio_ty < prio then fprintf ff ")" in
  ptype 0 ff ty

let ptype ff ty =
  let ty = Types.remove_dependences ty in
  Ptypes.output ff ty

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
  fprintf ff "@[<hov 2>%a_%s %a@ %a@]"
	  instance_name i_opt m instance i_opt
	  (print_list_r (exp 3) "" "" "") e_list

and var ff left =
  match left with
  | Oleft_name(n) -> fprintf ff "@[!%a@]" name n
  | _ -> left_value ff left

and left_state_value ff left =
  match left with
  | Oself -> fprintf ff "self."
  | Oleft_instance_name(n) -> fprintf ff "self.%a" name n
  | Oleft_state_global(ln) -> longname ff ln
  | Oleft_state_name(n) -> fprintf ff "self.%a" name n
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

and letvar ff n is_mutable ty e_opt i =
  let s = if is_mutable then "" else "ref " in
  match e_opt with
  | None ->
     fprintf ff "@[<v 0>let %a = %s(Obj.magic (): %a) in@ %a@]"
	     name n s ptype ty (inst 0) i
  | Some(e0) ->
     fprintf ff "@[<v 0>let %a = %s(%a:%a) in@ %a@]"
	     name n s (exp 0) e0 ptype ty (inst 0) i

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
  | Ovar(is_mutable, n) ->
     fprintf ff "@[%s%a@]" (if is_mutable then "" else "!") local n
  | Ostate(l) -> left_state_value ff l
  | Oaccess(e, eidx) ->
      fprintf ff "%a.(@[%a@])" (exp prio_e) e (exp prio_e) eidx
  | Ovec(e, se) ->
     (* make a vector *)
     let print_vec ff e se =
       match e with
       | Oconst _ ->
	  fprintf ff "@[<hov 2>Array.make@ (%a)@ (%a)@]"
		  (psize prio_e) se (exp prio_e) e
       | Ovec(e1, s2) ->
	  fprintf ff "@[<hov 2>Array.make_matrix@ (%a)@ (%a)@ (%a)@]"
		  (psize prio_e) se (psize prio_e) s2 (exp prio_e) e1
       | _ -> fprintf ff "@[<hov 2>Array.init@ @[(%a)@]@ @[(fun _ -> %a)@]@]"
		      (psize prio_e) se (exp prio_e) e in
     print_vec ff e se
  | Oupdate(se, e1, i, e2) ->
     (* returns a fresh vector [_t] of size [se] equal to [e2] except at *)
     (* [i] where it is equal to [e2] *)
     fprintf ff "@[(let _t = Array.copy (%a) in@ _t.(%a) <- %a; _t)@]"
             (exp 0) e1 (exp 0) i (exp 0) e2
  | Oslice(e, s1, s2) ->
     (* returns a fresh vector [_t] of size [s1+s2] *)
     (* with _t.(i) = e.(i + s1) for all i in [0..s2-1] *)
     fprintf ff "@[(let _t = Array.make %a %a.(0) in @ \
                    for i = 0 to %a - 1 do @ \
                      _t.(i) <- %a.(i+%a) done; @ \
                    _t)@]"
             (psize 2) s1 (exp 2) e
             (psize 0) s2
             (exp 2) e (psize 0) s1
  | Oconcat(e1, s1, e2, s2) ->
     (* returns a fresh vector [_t] of size [s1+s2] *)
     (* with _t.(i) = e1.(i) forall i in [0..s1-1] and *)
     (* _t.(i+s1) = e2.(i) forall i in [0..s2-1] *)
     fprintf ff "@[(let _t = Array.make (%a+%a) %a.(0) in @ \
                    Array.blit %a 0 _t 0 %a; @ \
                    Array.blit %a 0 _t %a; @ \
                    _t)@]"
             (psize 0) s1 (psize 0) s2 (exp 2) e1
             (exp 2) e1 (psize 0) s1
             (exp 2) e2 (psize 0) s2
  | Otuple(e_list) ->
      fprintf ff "@[<hov2>%a@]" (print_list_r (exp prio_e) "("","")") e_list
  | Oapp(e, e_list) ->
      fprintf ff "@[<hov2>%a %a@]"
        (exp (prio_e + 1)) e (print_list_r (exp (prio_e + 1)) """""") e_list
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
        (exp 0) e (exp prio_e) e1 (exp prio_e) e2
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
    | Oletvar(x, is_mutable, ty, e_opt, i) -> letvar ff x is_mutable ty e_opt i
    | Omatch(e, match_handler_l) ->
        fprintf ff "@[<v2>begin @[match %a with@ @[%a@]@] end@]"
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
       else fprintf
              ff "@[<hv>%a@]" (print_list_r (inst (prio_i + 1)) "" ";" "") i_list
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

and match_handler ff { w_pat = pat; w_body = b } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" pattern pat (inst 0) b


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

(** Define the data-type for the internal state of a machine *)
(* A prefix "_" is added to the name of the machine to avoid *)
(* name conflicts *)
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
  then fprintf ff "@[type _%s = unit@.@.@]" f
  else
    fprintf ff "@[<v 2>type @[%a@] _%s =@ { @[%a@] }@.@.@]"
            (print_list_r (fun ff s -> fprintf ff "'%s" s) "("","")") params
            f
            (print_list_r one_entry """;""") entries


(** Print the method as a function *)
let pmethod f ff { me_name = me_name; me_params = pat_list;
                   me_body = i; me_typ = ty } =
  fprintf ff "@[<v 2>let %s_%s self %a =@ (%a:%a) in@]"
          f (method_name me_name) pattern_list pat_list (inst 2) i ptype ty

(* create an array of type t[n_1]...[n_k] *)
let array_make print arg ff ie_size =
  let rec array_rec ff = function
    | [] -> fprintf ff "%a" print arg
    | ie :: ie_size ->
       fprintf ff "@[<hov>Array.init %a@ (fun _ -> %a)@]"
	       (exp 3) ie array_rec ie_size in
  array_rec ff ie_size

let rec array_of e_opt ty ff ie_size =
  let exp_of ff (e_opt, ty) =
    match e_opt, ty with
    | Some(e), _ -> exp 2 ff e
    | _ -> fprintf ff "(Obj.magic (): %a)" ptype ty in
  match ie_size with
  | [] -> exp_of ff (e_opt, ty)
  | [ie] -> fprintf ff "Array.make %a %a" (exp 3) ie exp_of (e_opt, ty)
  | ie :: ie_list ->
     fprintf ff
	     "@[<hov 2>Array.init %a@ (fun _ -> %a)@]" (exp 3) ie
	     (array_of e_opt ty) ie_list

(* Print initialization code *)
let print_initialize ff i_opt =
  match i_opt with
  | None -> fprintf ff "()" | Some(i) -> fprintf ff "%a" (inst 0) i

(** Print the allocation function *)
let palloc f i_opt memories ff instances =
  let print_memory ff { m_name = n; m_value = e_opt;
			m_typ = ty; m_kind = k_opt; m_size = m_size } =
    match k_opt with
    | None ->
       (* discrete state variable *)
       begin
	 match e_opt with
         | None ->
	    fprintf ff "@[%a = %a@]" name n
		    (array_make (fun ff _ -> fprintf ff "(Obj.magic (): %a)"
						     ptype ty) ())
		    m_size
         | Some(e) ->
	    fprintf ff "@[%a = %a@]" name n
		    (array_make exp_with_typ (e, ty)) m_size
       end
    | Some(m) ->
       match m with
       | Deftypes.Zero ->
	  fprintf ff "@[%a = @[<hov 2>{ zin = %a;@ zout = %a }@]@]"
		  name n (array_of e_opt Initial.typ_bool) m_size
		  (array_of (Some(Oconst(Ofloat(1.0)))) Initial.typ_float)
		  m_size
       | Deftypes.Cont ->
	  fprintf ff "@[%a = @[<hov 2>{ pos = %a; der = %a }@]@]"
		  name n (array_of e_opt ty) m_size
		  (* the default value of a derivative must be zero *)
		  (array_of (Some(Oconst(Ofloat(0.0)))) ty) m_size
       | Deftypes.Horizon | Deftypes.Period
       | Deftypes.Encore | Deftypes.Major ->
	  fprintf ff "%a = %a" name n (array_of e_opt ty) m_size in

  let print_instance ff { i_name = n; i_machine = ei;
			  i_kind = k; i_params = e_list; i_size = ie_size } =
    fprintf ff "@[%a = %a (* %s *)@ @]" name n
	    (array_make (fun ff n -> fprintf ff "%a_alloc ()" name n) n)
	    ie_size (kind k)  in
  if memories = []
  then if instances = []
       then fprintf ff "@[let %s_alloc _ = %a in@]" f print_initialize i_opt
       else
         fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,%a@] in@]"
                 f print_initialize i_opt
                 (print_record print_instance) instances
  else if instances = []
  then
    fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,%a@] in@]"
            f print_initialize i_opt (print_record print_memory) memories
  else
    fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,{ @[%a@,%a@] }@] in@]"
            f
            print_initialize i_opt
            (print_list_r print_memory """;"";") memories
            (print_list_r print_instance """;""") instances

(* A copy method that recursively copy an internal state. *)
(* This solution does not work at the moment when the program has *)
(* forall loops. *)
(* [copy source dest] recursively copies the containt of [source] into [dest] *)
let pcopy f memories ff instances =
  (* copy a memory [n] which is an array t[s1]...[sn] *)
  let array_copy print ff ie_size =
    let rec array_rec print ff = function
      | [] -> print ff ()
      | _ :: ie_size ->
	 fprintf ff "@[<hov>Array.map (fun xi -> %a) %a@]"
		 (array_rec (fun ff _ -> fprintf ff "xi")) ie_size print () in
    match ie_size with
    | [] -> print ff ()
    | _ -> array_rec print ff ie_size in
  
  let copy_memory ff
		  { m_name = n; m_kind = k_opt; m_typ = ty; m_size = m_size } =
    match k_opt with
    | None ->
       (* discrete state variable *)
       fprintf ff "@[dest.%a <- %a@]" name n
	       (array_copy (fun ff _ -> fprintf ff "source.%a" name n)) m_size
    | Some(m) ->
       match m with
       | Deftypes.Zero ->
	  fprintf ff "@[<hov0>dest.%a.zin <- %a;@,dest.%a.zout <- %a @]"
		  name n
		  (array_copy (fun ff _ -> fprintf ff "source.%a.zin" name n))
		  m_size
		  name n
		  (array_copy (fun ff _ -> fprintf ff "source.%a.zout" name n))
		  m_size
       | Deftypes.Cont ->
	  fprintf ff "@[<hov0>dest.%a.pos <- %a;@,dest.%a.der <- %a @]"
		  name n
		  (array_copy (fun ff _ -> fprintf ff "source.%a.pos" name n))
		  m_size
		  name n
		  (array_copy (fun ff _ -> fprintf ff "source.%a.der" name n))
		  m_size
       | Deftypes.Horizon | Deftypes.Period
       | Deftypes.Encore | Deftypes.Major ->
	  fprintf ff "@[dest.%a <- source.%a@]" name n name n in
  let copy_instance ff { i_name = n; i_machine = ei;
			  i_kind = k; i_params = e_list; i_size = ie_size } =
    fprintf ff "@[%a (* %s *)@]"
	    (array_make
	       (fun ff n ->
		fprintf ff "@[%a_copy source.%a dest.%a@]" name n name n name n)
	       n)
	    ie_size (kind k)  in
  if memories = []
  then if instances = []
       then fprintf ff "@[let %s_copy source dest = () in@]" f
       else
         fprintf ff "@[<v 2>let %s_copy source dest =@ @[%a@] in@]"
                 f (print_list_r copy_instance "" ";" "") instances
  else if instances = []
  then
    fprintf ff "@[<v 2>let %s_copy source dest =@ @[%a@] in@]"
            f (print_list_r copy_memory "" ";" "") memories
  else
    fprintf ff "@[<v 2>let %s_copy source dest =@ @[%a@,%a@] in@]"
            f
            (print_list_r copy_memory "" ";" ";") memories
            (print_list_r copy_instance "" ";" "") instances

	    
(* print an entry [let n_alloc, n_step, n_reset, ... = f ... in] *)
(* for every instance *)
let def_instance_function ff { i_name = n; i_machine = ei; i_kind = k;
			       i_params = e_list; i_size = ie_size } =
  (** Define the method *)
  let method_name ff me_name =
    let m = method_name me_name in
    fprintf ff "%s = %a_%s" m name n m in

  let list_of_methods ff m_list =  print_list_r method_name """;""" ff m_list in

  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany | Deftypes.Tdiscrete(false) -> ()
  | _ -> let m_name_list = expected_list_of_methods k in
	 let k = constructor_for_kind k in
	 fprintf ff
		 "@[let %s { alloc = %a_alloc; %a } = %a %a in@]"
		 k name n list_of_methods m_name_list
		 (exp 0) ei (print_list_r (exp 1) "" " " "") e_list

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
let machine f ff { ma_kind = k;
                   ma_params = pat_list;
		   ma_initialize = i_opt;
		   ma_memories = memories;
                   ma_instances = instances;
                   ma_methods = m_list } =
  (* print either [(f)] *)
  (* or [k { alloc = f_alloc; m1 = f_m1; ...; mn = f_mn }] *)
  let tuple_of_methods ff m_name_list =
    match k with
    | Deftypes.Tstatic _ | Deftypes.Tany -> fprintf ff "%s" f
    | Deftypes.Tdiscrete _
    | Deftypes.Tcont 
    | Deftypes.Tproba ->
       let method_name ff me_name =
	 let m = method_name me_name in
	 fprintf ff "@[%s = %s_%s@]" m f m in
       let k = constructor_for_kind k in
       let m_name_list =
	 List.map (fun { me_name = me_name } -> me_name) m_list in
       let m_name_list = extra_methods m_name_list in
       fprintf ff "@[%s { alloc = %s_alloc; %a }@]"
	       k f (print_list_r method_name "" ";" "") m_name_list in

  (* print the type for [f] *)
  def_type_for_a_machine ff f memories instances;
  (* print the code for [f] *)
  if !Misc.with_copy then
    fprintf ff
	    "@[<hov 2>let %s %a = @ @[@[%a@]@ @[%a@]@ @[%a@]@ @[%a@]@ %a@]@.@]"
	  f
	  pattern_list pat_list
	  (print_list_r def_instance_function "" "" "") instances
	  (palloc f i_opt memories) instances
	  (pcopy f memories) instances
	  (print_list_r (pmethod f) """""") m_list
	  tuple_of_methods m_list
  else
    fprintf ff "@[<hov 2>let %s %a = @ @[@[%a@]@ @[%a@]@ @[%a@]@ %a@]@.@]"
	  f
	  pattern_list pat_list
	  (print_list_r def_instance_function "" "" "") instances
	  (palloc f i_opt memories) instances
	  (print_list_r (pmethod f) """""") m_list
	  tuple_of_methods m_list

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
