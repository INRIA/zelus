(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
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

(** Priorities *)
let priority e =
  match e.desc with
    | Oconst _ | Oconstr0 _| Oglobal _ | Olocal _ | Oarray_element _
    | Orecord _ | Orecord_access _ | Otypeconstraint _ | Ofor _
    | Otuple _ -> 3
    | Oconstr1 _ | Oapp _ | Ostep _ | Oreset _
    | Oassign _ | Oarray_assign _ -> 2 
    | Olet _ | Oletvar _ | Oifthenelse _ | Omatch _ -> 1
    | Osequence _ -> 0

(** Flag to print a machine as a collection of functions or a class *)
let print_as_functions = ref false

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

let is_otypearrow ty = match ty.desc with
  | Otypearrow _ -> true
  | _ -> false

let rec ptype ff ty = match ty.desc with
  | Otypevar(s) -> fprintf ff "'%s" s
  | Otypearrow(ty1, ty2) when is_otypearrow ty1 ->
      fprintf ff "(%a) ->@ %a" ptype ty1 ptype ty2
  | Otypearrow(ty1, ty2) -> fprintf ff "%a ->@ %a" ptype ty1 ptype ty2
  | Otypetuple(ty_list) ->
      fprintf ff "@[<hov2>%a@]" (print_list_r ptype "("" *"")") ty_list
  | Otypeconstr(ln, ty_list) ->
      fprintf ff "@[<hov2>%a@]%a" 
        (print_list_r_empty ptype "("","")") ty_list longname ln
  | Otypeobject(n_ty_list) ->
      fprintf ff "@[<hov2><%a>@]"
        (print_list_l (print_couple shortname ptype """ :""") "<"";"">")
        n_ty_list

let rec pattern ff pat = match pat.desc with
  | Owildpat -> fprintf ff "_"
  | Oconstpat(i) -> immediate ff i
  | Oconstr0pat(lname) -> longname ff lname
  | Oconstr1pat(lname, pat_list) ->
      fprintf ff "@[%a%a@]"
        longname lname (print_list_r pattern "("","")") pat_list
  | Ovarpat(n) -> name ff n
  | Otuplepat(pat_list) ->
      pattern_comma_list ff pat_list
  | Oaliaspat(p, n) -> fprintf ff "%a as %a" pattern p name n
  | Oorpat(pat1, pat2) -> fprintf ff "%a | %a" pattern pat1 pattern pat2
  | Otypeconstraintpat(p, ty_exp) ->
      fprintf ff "(%a: %a)" pattern p ptype ty_exp
  | Orecordpat(n_pat_list) ->
      print_record (print_couple longname pattern """ =""") ff n_pat_list

and pattern_list ff pat_list =
  match pat_list with
    | [] -> fprintf ff "()"
    | _ -> fprintf ff "@[%a@]" (print_list_r pattern """""") pat_list

and pattern_comma_list ff pat_list =
  fprintf ff "@[%a@]" (print_list_r pattern "("","")") pat_list

(** Print the call to the step and reset methods *)
and step lname ff o =
  if !print_as_functions then fprintf ff "%a_step self.%a" longname lname name o
  else fprintf ff "%a.step" name o

and reset lname ff o = 
  if !print_as_functions 
  then fprintf ff "%a_reset self.%a" longname lname name o
  else fprintf ff "%a.reset()" name o

and assign ff (n, k) = 
  match k with
    | Mem -> 
        if !print_as_functions then fprintf ff "self.%a %s" name n "<-"
        else fprintf ff "%a %s" name n "<-"
    | _ -> fprintf ff "%a %s" name n ":="

and local ff n sort =
    fprintf ff "%s%a"
      (match sort with 
        | Val -> "" | Var -> "!" 
        | Mem -> if !print_as_functions then "self." else "")
      name n

and letvar ff n ty opt_e e =
  match opt_e with
    | None -> 
        if !print_as_functions
        then fprintf ff "@[<v 0>let %a = ref (Obj.magic (): %a) in@ %a@]" 
                name n Ptypes.output ty (exp 0) e
        else fprintf ff "@[<v 0>var %a: %a in@ %a@]" 
                name n Ptypes.output ty (exp 0) e
    | Some(e0) -> 
        if !print_as_functions
        then fprintf ff "@[<v 0>let %a = ref (%a:%a) in@ %a@]" 
          name n (exp 0) e0 Ptypes.output ty (exp 0) e
        else fprintf ff "@[<v 0>var %a: %a = %a in@ %a@]" 
          name n Ptypes.output ty (exp 0) e0 (exp 0) e
  
and exp prio ff e = 
  let prio_e = priority e in
  if prio_e < prio then fprintf ff "(";
  begin match e.desc with
  | Oconst(i) -> immediate ff i
  | Oconstr0(lname) -> longname ff lname
  | Oconstr1(lname, e_list) ->
      fprintf ff "@[%a%a@]"
        longname lname (print_list_r (exp 1) "("","")") e_list
  | Oglobal(ln) -> longname ff ln
  | Olocal(n, sort) -> local ff n sort
  | Oarray_element(n, eidx) ->
      fprintf ff "%a.{@[%a@]}" name n (exp 1) eidx
  | Otuple(e_list) ->
      fprintf ff "@[<hov2>%a@]" (print_list_r (exp 2) "("","")") e_list
  | Oapp(ln, []) ->
      fprintf ff "@[<hov2>%a ()@]" longname ln
  | Oapp(ln, e_list) ->
      fprintf ff "@[<hov2>%a %a@]" 
        longname ln (print_list_r (exp 3) """""") e_list
  | Ostep(ln, o, e_list) ->
      fprintf ff "@[<hov2>%a %a@]" (step ln) o
        (print_list_r (exp 3) """""") e_list
  | Oreset(ln, o) ->
      fprintf ff "@[<hov2>%a@]" (reset ln) o
  | Orecord(r) ->
      print_record (print_couple2 longname (exp 1) """ =""("")") ff r
  | Orecord_access(e, lname) ->
      fprintf ff "%a.%a" (exp prio_e) e longname lname
  | Otypeconstraint(e, ty_e) -> 
      fprintf ff "@[(%a : %a)@]" (exp prio_e) e ptype ty_e
  | Olet(pat_exp_list, e) -> 
      fprintf ff "@[<v 0>%a@ %a@]"
        (print_list_l pat_exp "let ""and "" in") pat_exp_list
        (exp (prio_e-1)) e
  | Oletvar(x, ty, e_opt, e) ->
      letvar ff x ty e_opt e
  | Omatch(e, match_handler_l) ->
      fprintf ff "@[<v2>match %a with@ %a@]"
        (exp 0) e (print_list_l match_handler """""") match_handler_l
  | Oifthenelse(e, e1, e2) ->
      fprintf ff "@[<hv>if %a@ @[<hv 2>then@ %a@]@ @[<hv 2>else@ %a@]@]"
        (exp 0) e (exp prio_e) e1 (exp prio_e) e2
  | Ofor(is_to, n, e1, e2, e3) ->
      fprintf ff "@[<hv>for %a = %a %s %a@ @[<hv 2>do@ %a@ done@]"
        name n (exp 0) e1 (if is_to then "to" else "downto") 
        (exp 0) e2 (exp 0) e3
  | Oassign(n, k, e) ->
      fprintf ff "@[%a %a@]" assign (n, k) (exp prio_e) e
  | Oarray_assign(n, eidx, e) ->
      fprintf ff "@[%a.{@[%a@]} <- %a@]" name n (exp 1) eidx (exp prio_e) e
  | Osequence(e1, e2) ->
      fprintf ff "@[%a;@\n%a@]" (exp (prio_e+2)) e1 (exp prio_e) e2
  end;
  if prio_e < prio then fprintf ff ")"

and expression e = exp 0 e

and pat_exp ff (p, e) = print_couple pattern (exp 0) """ =""" ff (p, e)

and match_handler ff { w_pat = pat; w_body = b } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" pattern pat (exp 0) b

let rec type_decl ff = function
  | Oabstract_type -> ()
  | Oabbrev(ty) -> ptype ff ty
  | Ovariant_type(constr_decl_list) ->
      print_list_l constr_decl """| """ ff constr_decl_list
  | Orecord_type(s_ty_list) ->
      print_record (print_couple pp_print_string ptype """ :""") ff s_ty_list

and constr_decl ff = function
  | Oconstr0decl(s) -> fprintf ff "%s" s
  | Oconstr1decl(s, ty_list) ->
      fprintf ff "%s of %a" s (print_list_l ptype """ *""") ty_list

let print_memory ff (n, (ty, e_opt)) =
  match e_opt with
    | None -> fprintf ff "%a : %a" name n Ptypes.output ty
    | Some(e) -> fprintf ff "%a : %a = %a" name n Ptypes.output ty (exp 0) e

let one_instance ff (n, ln) = fprintf ff "@[%a : %a@]" name n longname ln
        
(** Define the data-type for the internal state of a machine *)
let def_type_for_a_machine ff f memories instances =
  let one_entry ff (n, m) = 
    fprintf ff "@[mutable %a : '%s@]" name n m in
  let i, params, entries = 
    List.fold_right
      (fun (n, _) (i, params, entries) -> 
        let m = Misc.int_to_alpha i in (i+1, m :: params, (n, m) :: entries))
      memories (0, [], []) in
  let _, params, entries = 
    List.fold_right
      (fun (n, _) (i, params, entries) -> 
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

(** Define the step and reset functions *)
let def_step_for_a_machine ff f pat_list e =
  fprintf ff "@[<v 2>let %s_step self %a =@ @[%a@]@.@.@]"
    f pattern_list pat_list 
    (exp 0) e

let def_reset_for_a_machine ff f e =
  fprintf ff "@[<v 2>let %s_reset self =@ %a@.@.@]" f (exp 0) e
    
(** Define the allocation function *)
let def_alloc_for_a_machine ff f memories instances =
  let one_memory ff (n, (ty, m)) = 
    match m with
      | None -> fprintf ff "@[%a = (Obj.magic (): %a)@]" name n Ptypes.output ty
      | Some(e) -> fprintf ff "@[%a = (%a: %a)@]" name n (exp 0) e Ptypes.output ty
  in
  let one_instance ff (n, ln) = 
    fprintf ff "@[%a = %a()@]" name n longname ln in
  if memories = [] then if instances = []
  then fprintf ff "@[let %s () = ()@.@.@]" f
    else 
      fprintf ff "@[<v 2>let %s () =@ { @[%a@] }@.@.@]"
        f (print_list_r one_instance """;""") instances
  else if instances = []
  then
    fprintf ff "@[<v 2>let %s () =@ { @[%a@] }@.@.@]"
      f (print_list_r one_memory """;""") memories
  else
    fprintf ff "@[<v 2>let %s () =@ { @[%a%a@] }@.@.@]"
      f
      (print_list_r one_memory """;"";") memories
      (print_list_r one_instance """;""") instances
  
(** Print a machine *)
let machine_as_a_class ff f { m_memories = memories;
                              m_instances = instances; m_step = (pat_list, e); 
                              m_reset = reset } =
  fprintf ff "@[<hov 2>let %s = machine {@,\
                  @[@[<v 2>memories %a@]@;\
                  @[@[<v 2>instances %a@]@;\
                  @[@[<v 2>step %a =@ @[%a@]@]@;\
                  @[<v 2>reset() =@ @[%a@]@]@]@]@]}\
              @.@.@]"
    f
    (print_list_r_empty print_memory """""") memories
    (print_list_r_empty one_instance """""") instances
    pattern_list pat_list
    (exp 0) e
    (exp 0) reset 

(** Print a machine as pieces with a type definition for the state *)
(** an a collection of functions *)
let machine_as_functions ff f { m_memories = memories;
                                m_instances = instances; m_step = (pat_list, e);
                                m_reset = reset } =
  def_type_for_a_machine ff f memories instances;
  def_alloc_for_a_machine ff f memories instances;
  def_step_for_a_machine ff f pat_list e;
  def_reset_for_a_machine ff f reset

let machine ff f m = 
  if !print_as_functions then machine_as_functions ff f m
  else machine_as_a_class ff f m

let implementation ff impl = match impl.desc with
  | Oletvalue(n, e) ->
      fprintf ff "@[<v 2>let %a = %a@.@.@]" shortname n (exp 0) e
  | Oletfun(n, pat_list, e) ->
      fprintf ff "@[<v 2>let %a %a =@ %a@.@.@]" 
        shortname n pattern_list pat_list (exp 0) e
  | Oletmachine(n, m) -> machine ff n m
  | Oopen(s) ->
      fprintf ff "@[open %s@.@]" s
  | Otypedecl(l) ->
      fprintf ff "@[%a@.@]"
        (print_list_lb
            (fun ff (s, s_list, ty_decl) ->
                  fprintf ff "%a%s =@ %a"
                    print_type_params s_list
                    s type_decl ty_decl)
            "type ""and """)
        l

let implementation_list ff as_functions impl_list = 
  print_as_functions := as_functions;
  fprintf ff "@[(* %s *)@.@]" header_in_file;
  List.iter (implementation ff) impl_list
