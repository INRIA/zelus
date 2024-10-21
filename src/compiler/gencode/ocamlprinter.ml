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

(* print object code as OCaml code *)

open Misc
open Obc
open Format
open Pp_tools
open Printer
open Oprinter


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
  | Eany -> fprintf ff "Obj.magic ()"
		    
		    
let default_list_of_methods = [Oaux.step; Oaux.reset]

let print_concrete_type ff ty =
  let priority =
    function | Etypevar _ | Etypeconstr _ | Etypevec _ | Etypesize _ -> 2
             | Etypetuple _ -> 2 | Etypefun _ -> 1 in
  let rec ptype prio ff ty =
    let prio_ty = priority ty in
    if prio_ty < prio then fprintf ff "(";
    begin match ty with
    | Etypevar(s) -> fprintf ff "'%s" s
    | Etypefun(k, ty_arg, ty_res) ->
      begin match k with
        | Fun ->
           fprintf ff "@[<hov2>%a ->@ %a@]"
              (ptype (prio_ty+1)) ty_arg (ptype prio_ty) ty
        | Node | Hybrid ->
           fprintf ff "@[<hov2>(%a, %a) node@]"
             (ptype (prio_ty+1)) ty_arg (ptype prio_ty) ty
        end
    | Etypetuple(ty_list) ->
       fprintf ff
	       "@[<hov2>%a@]" (print_list_r (ptype prio_ty) "("" *"")") ty_list
    | Etypeconstr(ln, ty_list) ->
       fprintf ff "@[<hov2>%a@]%a"
               (print_list_r_empty (ptype 2) "("","")") ty_list longname ln
    | Etypevec(ty_arg, si) ->
       fprintf ff "@[%a %a@]" (ptype prio_ty) ty_arg
               longname (Lident.Modname Initial.array_ident)
    | Etypesize(is_singleton, si) ->
       fprintf ff "@[%a@]" longname (Lident.Modname Initial.array_ident)
     end;
    if prio_ty < prio then fprintf ff ")" in
  ptype 0 ff ty

let ptype ff ty = print_concrete_type ff ty

(* Print the call to a method *)
and method_call ff { met_name; met_instance; met_args } =
  let m = method_name met_name in
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
	  instance_name met_instance m instance met_instance
	  (print_list_r (exp 3) "" "" "") met_args

and var ff left =
  match left with
  | Eleft_name(n) -> fprintf ff "@[!%a@]" name n
  | _ -> left_value ff left

and left_state_value ff left =
  match left with
  | Eself -> fprintf ff "self."
  | Eleft_instance_name(n) -> fprintf ff "self.%a" name n
  | Eleft_state_global(ln) -> longname ff ln
  | Eleft_state_name(n) -> fprintf ff "self.%a" name n
  | Eleft_state_record_access(left, n) ->
     fprintf ff "@[%a.%a@]" left_state_value left longname n
  | Eleft_state_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_state_value left (exp 0) idx
  | Eleft_state_primitive_access(left, a) ->
     fprintf ff "@[%a%s@]" left_state_value left
       (Oprinter.state_primitive_access a)

and assign ff left e =
  match left with
  | Eleft_name(n) ->
     fprintf ff "@[<v 2>%a := %a@]" name n (exp 2) e
  | _ ->
     fprintf ff "@[<v 2>%a <- %a@]" left_value left (exp 2) e

and assign_state ff left e =
  match left with
  | Eleft_state_global(gname) ->
     fprintf ff "@[<v 2>%a := %a@]" longname gname (exp 2) e
  | _ -> fprintf ff "@[<v 2>%a <- %a@]" left_state_value left (exp 2) e

and letvar ff n is_mutable ty e_opt e =
  let s = if is_mutable then "" else "ref " in
  match e_opt with
  | None ->
     fprintf ff "@[<v 0>let %a = %s(Obj.magic (): %a) in@ %a@]"
	     name n s ptype ty (exp 0) e
  | Some(e0) ->
     fprintf ff "@[<v 0>let %a = %s(%a:%a) in@ %a@]"
	     name n s (exp 0) e0 ptype ty (exp 0) e

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
  | Evar { is_mutable; id } ->
     fprintf ff "@[%s%a@]" (if is_mutable then "" else "!") name id
  | Estate_access(l) -> left_state_value ff l
  | Etuple(e_list) ->
      fprintf ff "@[<hov2>%a@]" (print_list_r (exp prio_e) "("","")") e_list
  | Eapp { f; arg_list } ->
      fprintf ff "@[<hov2>%a %a@]"
        (exp (prio_e + 1)) f (print_list_r (exp (prio_e + 1)) """""") arg_list
  | Emethodcall m -> method_call ff m
  | Erecord(label_e_list) ->
     print_list_r
       (print_record longname (exp 0) "" " =" "") "{" ";" "}" ff label_e_list
  | Erecord_access { label; arg } ->
     fprintf ff "%a.%a" (exp prio_e) arg longname label
  | Erecord_with(e_record, label_e_list) ->
     fprintf ff "@[{ %a with %a }@]"
       (exp prio_e) e_record
       (print_list_r
          (print_record longname (exp 0) "" " =" "") "{" ";" "}") label_e_list
  | Etypeconstraint(e, ty_e) ->
      fprintf ff "@[(%a : %a)@]" (exp prio_e) e print_concrete_type ty_e
  | Eifthenelse(e, e1, e2) ->
      fprintf ff "@[<hv>if %a@ @[<hv 2>then@ %a@]@ @[<hv 2>else@ %a@]@]"
        (exp 0) e (exp prio_e) e1 (exp prio_e) e2
  | Elet(p, e1, e2) ->
     fprintf ff "@[<v 0>let %a in@ %a@]" pat_exp (p, e1) (exp (prio_e - 1)) e2
  | Eletvar { id; is_mutable; ty; e_opt; e } ->
     letvar ff id ty e_opt e
  | Ematch(e, match_handler_l) ->
     fprintf ff "@[<v2>match %a with@ @[%a@]@]"
       (exp 0) e
       (print_list_l match_handler """""") match_handler_l
  | Efor { index; left; right; e } ->
     fprintf ff "@[<hv>for %a = %a to %a@ @[<hv 2>do@ %a@ done@]@]"
       name index (exp 0) left (exp 0) right (exp 0) e
  | Ewhile { cond; e } ->
     fprintf ff "@[<hv>while %a do %a done@]@]"
       (exp 0) cond (exp 0) e
  | Eassign(left, e) -> assign ff left e
  | Eassign_state(left, e) -> assign_state ff left e
  | Esequence(e_list) ->
     if e_list = []
     then fprintf ff "()"
     else
       fprintf ff
         "@[<hv>%a@]" (print_list_r (exp 1) "" ";" "") e_list
  | Eget { e; size} ->
     fprintf ff "%a.(@[%a@])" (exp prio_e) e (psize 0) size
  | Eupdate { e; index; arg } ->
     (* returns a fresh vector [_t] of size [se] equal to [e2] except at *)
     (* [i] where it is equal to [e2] *)
     fprintf ff "@[(let _t = Array.copy (%a) in@ _t.(%a) <- %a; _t)@]"
             (exp 0) e (psize 0) index (exp 0) arg
  | Emake { e; size } ->
     (* make a vector *)
     let print_vec ff e se =
       match e with
       | Econst _ ->
	  fprintf ff "@[<hov 2>Array.make@ (%a)@ (%a)@]"
                                  (psize prio_e) se (exp prio_e) e
       | Emake { e; size } ->
	  fprintf ff "@[<hov 2>Array.make_matrix@ (%a)@ (%a)@ (%a)@]"
                      (psize prio_e) se (psize prio_e) size (exp prio_e) e
       | _ -> fprintf ff "@[<hov 2>Array.init@ @[(%a)@]@ @[(fun _ -> %a)@]@]"
		      (psize prio_e) se (exp prio_e) e in
     print_vec ff e size
  | Eslice { e; left; right; length } ->
     (* returns a fresh vector [_t] of size [s1+s2] *)
     (* with _t.(i) = e.(i + s1) for all i in [0..s2-1] *)
     fprintf ff "@[(let _t = Array.make %a %a.(0) in @ \
                    for i = 0 to %a - 1 do @ \
                      _t.(i) <- %a.(i+%a) done; @ \
                    _t)@]"
             (psize 2) length (exp 2) e (psize 0) right
             (exp 2) e (psize 0) left
  | Econcat { left; left_size; right; right_size } ->
     (* returns a fresh vector [_t] of size [s1+s2] *)
     (* with _t.(i) = e1.(i) forall i in [0..s1-1] and *)
     (* _t.(i+s1) = e2.(i) forall i in [0..s2-1] *)
     fprintf ff "@[(let _t = Array.make (%a+%a) %a.(0) in @ \
                    Array.blit %a 0 _t 0 %a; @ \
                    Array.blit %a 0 _t %a; @ \
                    _t)@]"
             (psize 0) left_size (psize 0) right_size (exp 2) left
             (exp 2) left (psize 0) left_size
             (exp 2) right (psize 0) right_size
  | Emachine(ma) -> machine ff ma
  | Efun _ -> ()
  end;
  if prio_e < prio then fprintf ff ")"

and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" pattern p (exp 0) e

and match_handler ff { m_pat; m_body } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" pattern m_pat (exp 0) m_body

(* Define the data-type for the internal state of a machine *)
(* A prefix "_" is added to the name of the machine to avoid *)
(* name conflicts *)
let def_type_for_a_machine ff f memories instances =
  let one_entry ff (n, m) =
    fprintf ff "@[mutable %a : '%s@]" name n m in
  let i, params, entries =
    List.fold_right
      (fun { m_name = n } (i, params, entries) ->
        let m = Genames.int_to_alpha i in (i+1, m :: params, (n, m) :: entries))
      memories (0, [], []) in
  let i, params, entries =
    List.fold_right
      (fun { i_name = n } (i, params, entries) ->
        let m = Genames.int_to_alpha i in (i+1, m :: params, (n, m) :: entries))
      instances (i, params, entries) in
  (* if the state is empty, produce the dummy state type [unit] *)
  if entries = []
  then fprintf ff "@[type _%s = unit@.@.@]" f
  else
    fprintf ff "@[<v 2>type @[%a@] _%s =@ { @[%a@] }@.@.@]"
      (Pp_tools.print_list_r (fun ff s -> fprintf ff "'%s" s)
         "("","")") params
      f
      (Pp_tools.print_list_r one_entry """;""") entries

let exp_with_typ ff (e, ty) = fprintf ff "(%a:%a)" (exp 2) e ptype ty

(* Print the method as a function *)
let pmethod f ff { me_name; me_params; me_body; me_typ } =
  fprintf ff "@[<v 2>let %s_%s self %a =@ (%a:%a) in@]"
    f (method_name me_name) pattern_list me_params (exp 2) me_body
    print_concrete_type me_typ

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

let constructor_for_kind = function
  | Node | Hybrid -> "Node"
  | Fun -> assert false

let expected_list_of_methods = default_list_of_methods

(* Print initialization code *)
let print_initialize ff e_opt =
  match e_opt with
  | None -> fprintf ff "()" | Some(e) -> fprintf ff "%a" (exp 0) e

(* Print the allocation function *)
let palloc f i_opt memories ff instances =
  let typ_bool = Etypeconstr(Lident.Modname (Initial.bool_ident), []) in
  let typ_float = Etypeconstr(Lident.Modname (Initial.float_ident), []) in
  let print_memory ff { m_name; m_value; m_typ; m_kind; m_size } =
    match m_kind with
    | Ediscrete ->
       (* discrete state variable *)
       begin
	 match m_value with
         | None ->
	    fprintf ff "@[%a = %a@]" name m_name
	      (array_make (fun ff _ -> fprintf ff "(Obj.magic (): %a)"
					 ptype m_typ) ())
	      m_size
         | Some(e) ->
	    fprintf ff "@[%a = %a@]" name m_name
	      (array_make exp_with_typ (e, m_typ)) m_size
       end
    | Ezero ->
       fprintf ff "@[%a = @[<hov 2>{ zin = %a;@ zout = %a }@]@]"
	 name m_name (array_of m_value typ_bool) m_size
	 (array_of (Some(Econst(Efloat(1.0)))) typ_float)
	 m_size
    | Econt ->
       fprintf ff "@[%a = @[<hov 2>{ pos = %a; der = %a }@]@]"
	 name m_name (array_of m_value m_typ) m_size
	 (* the default value of a derivative must be zero *)
	 (array_of (Some(Econst(Efloat(0.0)))) m_typ) m_size
    | Ehorizon | Emajor ->
       fprintf ff "%a = %a" name m_name (array_of m_value m_typ) m_size in
  
  let print_instance ff { i_name; i_machine; i_kind; i_params; i_sizes } =
    fprintf ff "@[%a = %a (* %s *)@ @]" name i_name
      (array_make (fun ff n -> fprintf ff "%a_alloc ()" name n) i_name)
      i_sizes (kind i_kind)  in
  if memories = []
  then if instances = []
       then fprintf ff "@[let %s_alloc _ = %a in@]" f print_initialize i_opt
       else
         fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,%a@] in@]"
           f print_initialize i_opt
           (Pp_tools.print_record print_instance) instances
  else if instances = []
  then
    fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,%a@] in@]"
      f print_initialize i_opt (Pp_tools.print_record print_memory) memories
  else
    fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,{ @[%a@,%a@] }@] in@]"
      f
      print_initialize i_opt
      (print_list_r print_memory """;"";") memories
      (print_list_r print_instance """;""") instances

(* print an entry [let n_alloc, n_step, n_reset, ... = f ... in] *)
(* for every instance *)
let def_instance_function ff { i_name; i_machine; i_kind; i_params; i_sizes } =
  (* Define the method *)
  let method_name ff me_name =
    let m = method_name me_name in
    fprintf ff "%s = %a_%s" m name i_name m in

  let list_of_methods ff m_list =  print_list_r method_name """;""" ff m_list in

  match i_kind with
  | Fun -> ()
  | Node | Hybrid ->
     let m_name_list = expected_list_of_methods in
     let k = constructor_for_kind i_kind in
     fprintf ff
       "@[let %s { alloc = %a_alloc; %a } = %a %a in@]"
       k name i_name list_of_methods m_name_list
       (exp 0) i_machine (print_list_r (exp 1) "" " " "") i_sizes

(* Print a machine as pieces with a type definition for the state *)
(* and a collection of functions *)
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
let machine f ff { ma_kind; ma_params; ma_initialize; ma_memories;
                   ma_instances; ma_methods } =
  (* print either [(f)] *)
  (* or [k { alloc = f_alloc; m1 = f_m1; ...; mn = f_mn }] *)
  let tuple_of_methods ff m_name_list =
    match ma_kind with
    | Fun -> fprintf ff "%s" f
    | Node | Hybrid ->
       let method_name ff me_name =
	 let m = method_name me_name in
	 fprintf ff "@[%s = %s_%s@]" m f m in
       let k = constructor_for_kind ma_kind in
       let m_name_list =
	 List.map (fun { me_name } -> me_name) ma_methods in
       fprintf ff "@[%s { alloc = %s_alloc; %a }@]"
	       k f (print_list_r method_name "" ";" "") m_name_list in

  (* print the type for [f] *)
  def_type_for_a_machine ff f ma_memories ma_instances;
  (* print the code for [f] *)
  fprintf ff "@[<hov 2>let %s %a = @ @[@[%a@]@ @[%a@]@ @[%a@]@ %a@]@.@]"
	  f
	  pattern_list ma_params
	  (print_list_r def_instance_function "" "" "") ma_instances
	  (palloc f ma_initialize ma_memories) ma_instances
	  (print_list_r (pmethod f) """""") ma_methods
	  tuple_of_methods ma_methods

let implementation ff impl = match impl with
  | Eletdef(n, e) ->
     fprintf ff "@[<v 2>let %a = %a@.@.@]" shortname n (exp 0) e
  | Eopen(s) ->
     fprintf ff "@[open %s@.@]" s
  | Etypedecl(l) ->
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
