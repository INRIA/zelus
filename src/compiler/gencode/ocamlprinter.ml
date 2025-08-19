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

(* print object code as OCaml code *)

open Misc
open Obc
open Format
open Pp_tools
module Printer = Printer.Make(Ptypinfo)

let longname ln = Oprinter.longname ln

(* Printing types. *)
(* [t1 -D-> t2] is [(t1, t2) node] *)
(* [t1 -C-> t2] is [(t1, t2) hnode] *)
(* [t1 -A-> t2], [t1 -S-> t2] are [t1 -> t2] *)
(* dependences are discarded *)
let ptype ff typ_exp =
  let open Zelus in
  let priority desc =
    match desc with
    | Etypevar _ | Etypeconstr _ | Etypevec _ -> 2 
    | Etypetuple _ -> 2 | Etypefun _ -> 1 in
  let rec ptype prio ff { desc } =
    let prio_ty = priority desc in
    if prio_ty < prio then fprintf ff "(";
    begin match desc with
    | Etypevar(s) -> fprintf ff "%s" s
    | Etypefun { ty_kind; ty_arg; ty_res } ->
        begin match ty_kind with
          | Kfun _ ->
              fprintf ff "@[<hov2>%a ->@ %a@]"
                (ptype (prio_ty+1)) ty_arg (ptype prio_ty) ty_res
          | Knode _ ->
              fprintf ff "@[<hov2>(%a, %a) Ztypes.node@]"
                (ptype (prio_ty+1)) ty_arg (ptype prio_ty) ty_res
        end
    | Etypetuple(ty_list) ->
       fprintf ff
	       "@[<hov2>%a@]" (print_list_r (ptype prio_ty) "("" *"")") ty_list
    | Etypeconstr(ln, ty_list) ->
       fprintf ff "@[<hov2>%a@]%a"
               (print_list_r_empty (ptype 2) "("","")") ty_list 
               longname ln
    | Etypevec(ty_arg, _) ->
       fprintf ff "@[%a %a@]" (ptype prio_ty) ty_arg
               longname (Lident.Modname Initial.array_ident)
    end;
    if prio_ty < prio then fprintf ff ")" in
  ptype 0 ff typ_exp

(* print a internal type *)
let p_internal_type ff typ =
  let typ_exp = Interface.type_expression_of_typ typ in
  ptype ff typ_exp

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

(* Define the data-type for the internal state of a machine *)
(* A prefix "_" is added to the name of the machine to avoid *)
(* name conflicts *)
let def_type_for_a_machine ma_name ma_memories ma_instances =
  let unit_type =
    let open Zelus in
    { desc = Etypeconstr(Lident.Modname(Initial.unit_ident), []);
    loc = Location.no_location } in
  let one_entry (n, m) =
    let open Zelus in
    (true, Ident.name n, { desc = Etypevar m; loc = Location.no_location }) in
  let i, params, entries =
    List.fold_right
      (fun { m_name = n } (i, params, entries) ->
        let m = Genames.int_to_alpha i in
        (i+1, m :: params, (n, m) :: entries))
      ma_memories (0, [], []) in
  let i, params, entries =
    List.fold_right
      (fun { i_name = n } (i, params, entries) ->
        let m = Genames.int_to_alpha i in
        (i+1, m :: params, (n, m) :: entries))
      ma_instances (i, params, entries) in
  (* if the state is empty, produce the dummy state type [unit] *)
  if entries = []
  then
    Etypedecl [Ident.name ma_name, [], Eabbrev(unit_type)]
  else
    Etypedecl
      [Ident.name ma_name, params, Erecord_type(List.map one_entry entries)]

(* Print the call to a method *)
let rec method_call ff { met_name; met_instance; met_args } =
  let m = Oprinter.method_name met_name in
  let instance_name ff i_opt =
    match i_opt with
    | None -> fprintf ff "self" | Some(o, _) -> Printer.name ff o in
  let instance ff i_opt =
    match i_opt with
    | None -> (* a call to the self machine *) fprintf ff "self"
    | Some(o, e_list) ->
       match e_list with
       | [] -> fprintf ff "self.%a" Printer.name o
       | e_list ->
	  fprintf ff "self.%a.%a" Printer.name o
		  (print_list_no_space
		     (print_with_braces (exp 3) "(" ")") "" "." "")
		  e_list in
  fprintf ff "@[<hov 2>%a_%s %a@ %a@]"
	  instance_name met_instance m instance met_instance
	  (print_list_r (exp 3) "" "" "") met_args

and print_self_name ff self = Printer.name ff self

and left_state_value ff left =
  match left with
  | Eself_state(self) -> print_self_name ff self
  | Eleft_instance_name { self; name } | Eleft_state_name { self; name } ->
        Format.fprintf ff "%a.%a" print_self_name self Printer.name name
  | Eleft_state_record_access { label; arg } ->
     fprintf ff "@[%a.%a@]" left_state_value arg longname label
  | Eleft_state_index(left, idx) ->
     fprintf ff "@[%a.(%a)@]" left_state_value left (exp 0) idx
  | Eleft_state_primitive_access(left, a) ->
     fprintf ff "@[%a.%s@]" left_state_value left
       (Oprinter.state_primitive_access a)

and assign ff left e =
  match left with
  | Eleft_name(n) ->
     fprintf ff "@[<v 2>%a := %a@]" Printer.name n (exp 2) e
  | _ ->
     fprintf ff "@[<v 2>%a <- %a@]" Oprinter.left_value left (exp 2) e

and assign_state ff left e =
  match left with
  | Eself_state(self) ->
     fprintf ff "@[<v 2>%a := %a@]" print_self_name self (exp 2) e
  | _ -> fprintf ff "@[<v 2>%a <- %a@]" left_state_value left (exp 2) e

and letvar ff n is_mutable ty e_opt e =
  let s = if is_mutable then "" else "ref " in
  match e_opt with
  | None ->
     fprintf ff "@[<v 0>let %a = %s(Obj.magic (): %a) in@ %a@]"
	     Printer.name n s p_internal_type ty (exp 0) e
  | Some(e0) ->
     fprintf ff "@[<v 0>let %a = %s(%a:%a) in@ %a@]"
	     Printer.name n s (exp 0) e0 p_internal_type ty (exp 0) e

and exp prio ff e =
  let prio_e = Oprinter.priority_exp e in
  if prio_e < prio then fprintf ff "(";
  begin match e with
  | Econst(i) -> immediate ff i
  | Econstr0 { lname } -> longname ff lname
  | Econstr1 { lname; arg_list } ->
      fprintf ff "@[%a%a@]"
        longname lname (print_list_r (exp prio_e) "("","")") arg_list
  | Eglobal { lname } -> longname ff lname
  | Evar { is_mutable; id } ->
     fprintf ff "@[%s%a@]" (if is_mutable then "!" else "") Printer.name id
  | Estate(l) -> left_state_value ff l
  | Etuple(e_list) ->
      Pp_tools.print_tuple (exp prio_e) ff e_list
  | Eapp { f; arg_list } ->
      fprintf ff "@[<hov2>%a %a@]"
        (exp (prio_e + 1)) f (print_list_r (exp (prio_e + 1)) """""") arg_list
  | Esizeapp { f; size_list } ->
      fprintf ff "@[<hov2>%a %a@]"
        (exp (prio_e + 1)) f
        (print_list_r (exp (prio_e + 1)) "" " " "") size_list
  | Emethodcall m -> method_call ff m
  | Erecord(label_e_list) ->
     print_list_r
       (Oprinter.print_record longname
          (exp 0) "" " =" "") "{" ";" "}" ff label_e_list
  | Erecord_access { label; arg } ->
     fprintf ff "%a.%a" (exp prio_e) arg longname label
  | Erecord_with(e_record, label_e_list) ->
     fprintf ff "@[{ %a with %a }@]"
       (exp prio_e) e_record
       (print_list_r
          (Oprinter.print_record longname (exp 0)
             "" " =" "") "{" ";" "}") label_e_list
  | Etypeconstraint(e, ty_e) ->
      fprintf ff "@[(%a : %a)@]" (exp prio_e) e ptype ty_e
  | Eifthenelse(e, e1, e2) ->
      fprintf ff "@[<hv>if %a@ @[<hv 2>then@ %a@]@ @[<hv 2>else@ %a@]@]"
        (exp 0) e (exp 1) e1 (exp 1) e2
  | Elet(p, e1, e2) ->
     fprintf ff "@[<v 0>let %a in@ %a@]" pat_exp (p, e1) (exp (prio_e - 1)) e2
  | Eletvar { id; is_mutable; ty; e_opt; e } ->
     letvar ff id is_mutable ty e_opt e
  | Eletmem(m_list, e) ->
     fprintf ff "@[<v 0>let %a in@ %a@]"
       (print_list_l print_memory "" "and " "") m_list (exp 0) e
  | Eletinstance(i_list, e) ->
     fprintf ff
       "@[<v 0>let %a in@ %a@]"
        (print_list_l print_instance "" "and " "") i_list (exp 0) e
  | Eletsizefun(is_rec, sizefun_list, e) ->
     fprintf ff
       "@[<v 0>let %s%a in@ %a@]" (if is_rec then "rec " else "")
       (print_list_l sizefun "" "and " "") sizefun_list (exp 0) e
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
  | Eget { e; index} ->
     fprintf ff "%a.(@[%a@])" (exp prio_e) e (exp 0) index
  | Eupdate { e; index; arg } ->
     (* returns a fresh vector [_t] of size [se] equal to [e2] except at *)
     (* [i] where it is equal to [e2] *)
     fprintf ff "@[(let _t = Array.copy (%a) in@ _t.(%a) <- %a; _t)@]"
             (exp 0) e (exp 0) index (exp 0) arg
  | Evec { e; size } ->
     (* make a vector *)
     let print_vec ff e se =
       match e with
       | Econst _ ->
	  fprintf ff "@[<hov 2>Array.make@ (%a)@ (%a)@]"
                                  (exp 0) se (exp prio_e) e
       | Evec { e; size } ->
	  fprintf ff "@[<hov 2>Array.make_matrix@ (%a)@ (%a)@ (%a)@]"
                      (exp 0) se (exp 0) size (exp prio_e) e
       | _ -> fprintf ff "@[<hov 2>Array.init@ @[(%a)@]@ @[(fun _ -> %a)@]@]"
		      (exp 0) se (exp prio_e) e in
     print_vec ff e size
  | Eslice { e; left; right } ->
     (* returns a fresh vector [_t] of size [s2-s1+1] *)
     (* with _t.(i) = e.(i + s1) for all i in [0..s2-1] *)
     fprintf ff "@[(let _t = Array.make %a %a.(0) in @ \
                    for i = 0 to %a - 1 do @ \
                      _t.(i) <- %a.(i+%a) done; @ \
                    _t)@]"
             (exp 0) left (exp 2) e (exp 0) right
             (exp 2) e (exp 0) left
  | Econcat { left; left_size; right; right_size } ->
     (* returns a fresh vector [_t] of size [s1+s2] *)
     (* with _t.(i) = e1.(i) forall i in [0..s1-1] and *)
     (* _t.(i+s1) = e2.(i) forall i in [0..s2-1] *)
     fprintf ff "@[(let _t = Array.make (%a+%a) %a.(0) in @ \
                    Array.blit %a 0 _t 0 %a; @ \
                    Array.blit %a 0 _t %a; @ \
                    _t)@]"
             (exp 0) left_size (exp 0) right_size (exp 2) left
             (exp 2) left (exp 0) left_size
             (exp 2) right (exp 0) right_size        
  | Earray_list(e_list) ->
     fprintf ff "[|%a|]"
        (Pp_tools.print_list_r (exp 0) "" ";" "") e_list
  | Etranspose { e; size_1; size_2 } ->
     (* returns a fresh vector of vectors [_t] *)
     (* with _t.(j).(i) = e.(i).(j) forall i in [0..s1-1], j in [0..s2-1] *)
     fprintf ff
       "@[<hov1>(let _s1 = %a and _s2 = %a and _v = %a in@ \
          let _t = Array.init _s1 (fun i -> Array.make _s2 _v.(0).(0)) in @ \
           for i = 0 to _s1 - 1 do @ \
            for j = 0 to _s2 - 1 do @ \
              _t.(j).(i) <- _v.(i).(j) @ \
        done @ \
        done; _t)@]"
       (exp 0) size_1 (exp 0) size_2 (exp 02) e
  | Ereverse { e; size } ->
     (* returns a fresh vector of vectors [_t] *)
     (* with _t.(i) = e.(s - i - 1) forall i in [0..s-1] *)
     fprintf ff
       "@<hov1>(let _s = %a and _v = %a in@ \
        for i = 0 to _s - 1 do @ \
        _t.(i) = _v.(_s - i - 1) @ \
        done; _t@]"
        (exp 0) size (exp 0) e
  | Eflatten { e; size_1; size_2 } ->
     (* returns a fresh vector of vectors [_t] *)
     (* with _t.(i*s2 + j) = e.(i).(j) forall i in [0..s1-1], j in [0..s2-1] *)
     fprintf ff
       "@[<hov1>(let _s1 = %a and _s2 = %a and _v = %a in@ \
        let _t = Array.make (_s1 * s_2) _v.(0).(0) in @ \
        for i = 0 to _s1 - 1 do @ \
            for j = 0 to _s2 - 1 do @ \
              _t.(i * _s2 + j) <- _v.(i).(j) @ \
        done @ \
        done; _t)@]"
       (exp 0) size_1 (exp 0) size_2 (exp 0) e
  | Emachine(ma) -> machine ff ma
  | Efun { pat_list; e } ->
     fprintf ff
       "@[<hov2>(fun@ %a ->@ %a)@]" 
       (Oprinter.pattern_list ptype) pat_list (exp 0) e
  end;
  if prio_e < prio then fprintf ff ")"

and sizefun ff { sf_id; sf_id_list; sf_e } =
  (* [id ... = e] *)
  fprintf ff
    "@[%a %a =@ %a@]" Printer.name sf_id
    (print_list_r Printer.name "" " " "") sf_id_list (exp 0) sf_e

and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" (Oprinter.pattern ptype) p (exp 0) e

and match_handler ff { m_pat; m_body } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" (Oprinter.pattern ptype) m_pat (exp 0) m_body

(* create an array of type t[n_1]...[n_k] *)
and array_make : 'a. (_ -> 'a -> _) -> 'a -> _ -> _ -> _ =
  fun print arg ff ie_size ->
  let rec array_rec ff = function
    | [] -> fprintf ff "%a" print arg
    | ie :: ie_size ->
       fprintf ff "@[<hov>Array.init %a@ (fun _ -> %a)@]"
	       (exp 3) ie array_rec ie_size in
  array_rec ff ie_size

and array_of e_opt ty ff ie_size =
  let exp_of ff (e_opt, ty) =
    match e_opt, ty with
    | Some(e), _ -> exp 2 ff e
    | _ -> fprintf ff "(Obj.magic (): %a)" p_internal_type ty in
  match ie_size with
  | [] -> exp_of ff (e_opt, ty)
  | [ie] -> fprintf ff "Array.make %a %a" (exp 3) ie exp_of (e_opt, ty)
  | ie :: ie_list ->
     fprintf ff
	     "@[<hov 2>Array.init %a@ (fun _ -> %a)@]" (exp 3) ie
	     (array_of e_opt ty) ie_list

(* Print the allocation function *)
and print_memory ff { m_name; m_value; m_typ; m_kind; m_size } =
  match m_kind with
  | None ->
     (* discrete state variable *)
     begin
       match m_value with
       | None ->
	  fprintf ff "@[%a = %a@]" Printer.name m_name
	    (array_make (fun ff _ -> fprintf ff "(Obj.magic (): %a)"
				       p_internal_type m_typ) ())
	    m_size
       | Some(e) ->
	  fprintf ff "@[%a = %a@]" Printer.name m_name
	    (array_make exp_with_typ (e, m_typ)) m_size
     end
  | Some(k) ->
     match k with
       Zero ->
        fprintf ff "@[%a = @[<hov 2>{ zin = %a;@ zout = %a }@]@]"
          Printer.name m_name (array_of m_value Initial.typ_bool) m_size
          (array_of (Some(Econst(Efloat(1.0)))) Initial.typ_float)
          m_size
     | Cont ->
        fprintf ff "@[%a = @[<hov 2>{ pos = %a; der = %a }@]@]"
          Printer.name m_name (array_of m_value m_typ) m_size
          (* the default value of a derivative must be zero *)
          (array_of (Some(Econst(Efloat(0.0)))) m_typ) m_size
     | Horizon | Major | Period | Encore | Time ->
        fprintf ff "%a = %a" Printer.name m_name (array_of m_value m_typ) m_size
     
    
and print_instance ff { i_name; i_machine; i_kind; i_params; i_size } =
    fprintf ff "@[%a = %a (* %s *)@ @]" Printer.name i_name
      (array_make (fun ff n -> fprintf ff "%a_alloc ()" Printer.name n) i_name)
      i_size (Oprinter.kind i_kind)

and exp_with_typ ff (e, ty) = fprintf ff "(%a:%a)" (exp 2) e p_internal_type ty

(* Print the method as a function *)
and pmethod f ma_self ff { me_name; me_params; me_body; me_typ } =
  fprintf ff "@[<v 2>let %s_%s %a %a =@ (%a:%a) in@]"
    f (Oprinter.method_name me_name) print_self_name ma_self
    (Oprinter.pattern_list ptype) me_params (exp 2) me_body
    p_internal_type me_typ

and constructor_for_kind = function
  | Deftypes.Tnode _ -> "Node"
  | Deftypes.Tfun _ -> assert false

and expected_list_of_methods = default_list_of_methods

(* Print initialization code *)
and print_initialize ff i_list =
  match i_list with
  | [] -> fprintf ff "()"
  | _ -> Pp_tools.print_list_r (exp 0) "" ";" "" ff i_list

and palloc f i_list memories ff instances =
  if memories = []
  then if instances = []
       then fprintf ff "@[let %s_alloc _ = %a in@]" f print_initialize i_list
       else
         fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,%a@] in@]"
           f print_initialize i_list
           (Pp_tools.print_record print_instance) instances
  else if instances = []
  then
    fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,%a@] in@]"
      f print_initialize i_list (Pp_tools.print_record print_memory) memories
  else
    fprintf ff "@[<v 2>let %s_alloc _ =@ @[%a;@,{ @[%a@,%a@] }@] in@]"
      f
      print_initialize i_list
      (print_list_r print_memory """;"";") memories
      (print_list_r print_instance """;""") instances

(* print an entry [let n_alloc, n_step, n_reset, ... = f ... in] *)
(* for every instance; the list of method is limited to the non local *)
(* (visible) ones *)
and def_instance_function ff { i_name; i_machine; i_kind; i_params; i_size } =
  (* Define the method *)
  let method_name ff me_name =
    let m = Oprinter.method_name me_name in
    fprintf ff "%s = %a_%s" m Printer.name i_name m in

  let list_of_methods ff m_list =  print_list_r method_name """;""" ff m_list in

  match i_kind with
  | Deftypes.Tfun _ -> ()
  | Deftypes.Tnode _ ->
     let m_name_list = expected_list_of_methods in
     let k = constructor_for_kind i_kind in
     fprintf ff
       "@[let %s { alloc = %a_alloc; %a } = %a %a in@]"
       k Printer.name i_name list_of_methods m_name_list
       (exp 0) i_machine (print_list_r (exp 1) "" " " "") i_params

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
 *   { alloc = f_alloc; step = f_step; reset = f_reset; ... } in
 * f *)
and machine ff { ma_name; ma_kind; ma_params; ma_initialize; ma_self; 
                 ma_memories; ma_instances; ma_methods; ma_assertion } =
  (* print either [(f)] *)
  (* or [k { alloc = f_alloc; m1 = f_m1; ...; mn = f_mn }] *)
  let f = Ident.name ma_name in
  let tuple_of_methods ff m_name_list =
    match ma_kind with
    | Deftypes.Tfun _ -> fprintf ff "%s" f
    | Deftypes.Tnode _ ->
       let method_name ff me_name =
	 let m = Oprinter.method_name me_name in
	 fprintf ff "@[%s = %s_%s@]" m f m in
       let k = constructor_for_kind ma_kind in
       let m_name_list =
	 List.map (fun { me_name } -> me_name) ma_methods in
       fprintf ff "@[%s { alloc = %s_alloc; %a }@]"
	       k f (print_list_r method_name "" ";" "") m_name_list in

  (* print the code for [f] *)
  fprintf ff "@[<hov 2>let %s %a = @ @[@[%a@]@ @[%a@]@ @[%a@]@ %a %a in@ %s@]@]"
    f
    (Oprinter.pattern_list ptype) ma_params
    (print_list_r def_instance_function "" "" "") ma_instances
    (palloc f ma_initialize ma_memories) ma_instances
    (print_list_r (pmethod f ma_self) """""") ma_methods
    (print_list_r machine "" "" "") ma_assertion 
    tuple_of_methods ma_methods f

(* computes the set of type declarations for representing the state *)
(* for every machines defined in expression [e]. This is done by a first step *)
let def_types acc impl =
  let rec def_types acc e =
    match e with
    | Econst _ | Econstr0 _ | Eglobal _ | Evar _ | Estate _ -> acc
    | Econstr1 { arg_list } | Etuple arg_list | Earray_list arg_list
      | Emethodcall { met_args = arg_list } | Esequence(arg_list)->
       List.fold_left def_types acc arg_list
    | Eapp { f; arg_list } ->
       List.fold_left def_types (def_types acc f) arg_list
    | Esizeapp { f; size_list } ->
       List.fold_left def_types (def_types acc f) size_list
    | Erecord(label_e_list) ->
       List.fold_left (fun acc { arg } -> def_types acc arg) acc label_e_list
    | Erecord_access { arg } -> def_types acc arg
    | Erecord_with(e_record, label_e_list) ->
       List.fold_left
         (fun acc { arg } -> def_types acc arg) (def_types acc e_record)
         label_e_list
    | Etypeconstraint(e, _) | Efun { e } -> def_types acc e
    | Eifthenelse(e, e1, e2) ->
       def_types (def_types (def_types acc e) e1) e2
    | Elet(_, e1, e2) -> def_types (def_types acc e1) e2
    | Eletvar { e } | Eletmem(_, e) | Eletinstance(_, e) -> def_types acc e
    | Eletsizefun(_, sizefun_list, e) ->
       let sizefun acc { sf_e } = def_types acc e in
       def_types (List.fold_left sizefun acc sizefun_list) e
    | Ematch(e, m_h) ->
       List.fold_left (fun acc { m_body } -> def_types acc m_body) acc m_h
    | Efor { left; right; e } | Eupdate { e; index = left; arg = right }
      | Eslice { e; left; right } ->
       def_types (def_types (def_types acc left) right) e
    | Ewhile { cond; e } | Eget { e; index = cond } | Evec { e; size = cond } ->
       def_types (def_types acc cond) e
    | Eassert(e) | Eassign(_, e) | Eassign_state(_, e) -> 
       def_types acc e
    | Econcat { left; left_size; right; right_size } ->
       def_types
         (def_types (def_types (def_types acc left) left_size) right) right_size
    | Etranspose { e; size_1; size_2 }
      | Eflatten { e; size_1; size_2 } ->
       def_types (def_types (def_types acc e) size_1) size_2
    | Ereverse { e; size } -> def_types (def_types acc e) size
    | Emachine { ma_name; ma_initialize;
                 ma_memories; ma_instances; ma_methods } ->
       let def_method acc { me_body } = def_types acc me_body in
       let acc = List.fold_left def_method acc ma_methods in
       def_type_for_a_machine ma_name ma_memories ma_instances :: acc in
  match impl with
  | Eletdef(n_e_list) ->
     List.fold_left (fun acc (n, e) -> def_types acc e) acc n_e_list
  | Eopen _ | Etypedecl _ -> acc     

let implementation ff impl =
  let print_n_list ff n_list =
    Pp_tools.print_list_r Printer.shortname "(" "," ")" ff n_list in
  match impl with
  | Eletdef(n_list_e_list) ->
     let print ff (n_list, e) =
       fprintf ff "@[<hov2>%a =@ %a@]" print_n_list n_list (exp 0) e in
     fprintf ff "@[<v0>let %a@.@]"
       (Pp_tools.print_list_l print "" "and " "") n_list_e_list
  | Eopen(s) ->
     fprintf ff "@[open %s@.@]" s
  | Etypedecl(l) ->
     let print ff (s, s_list, ty_decl) =
       fprintf ff "%a%s =@ %a" Oprinter.print_type_params s_list
         s Oprinter.type_decl ty_decl in
     fprintf ff "@[%a@.@]" (print_list_l print "type ""and """) l


let implementation_list ff impl_list =
  fprintf ff "@[(* %s *)@.@]" header_in_file;
  fprintf ff "@[open Ztypes@.@]";
  (* first extract the set of type definitions for states *)
  let ty_decl_list = List.fold_left def_types [] impl_list in
  List.iter (implementation ff) ty_decl_list;
  List.iter (implementation ff) impl_list

let program ff { p_impl_list } =
  implementation_list ff p_impl_list
