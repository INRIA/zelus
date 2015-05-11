(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
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
    | Oconst _ | Oconstr0 _| Oglobal _ | Olocal _ | Ostate _ | Oindex _
    | Orecord _ | Orecord_access _ | Otypeconstraint _ | Ofor _ | Owhile _
    | Otuple _ -> 3
    | Oconstr1 _ | Oapp _ | Omethod _ | Oassign _ | Oassign_state _ -> 2
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

let kind = function
  | Deftypes.Tany | Deftypes.Tdiscrete _ -> "discrete"
  | Deftypes.Tcont -> "continuous"

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

(** Print the call to a method *)
and method_call ff { c_machine = lname; c_method_name = m; c_instance = i_opt } =
  let m = method_name m in
  let instance ff i_opt =
    match i_opt with
    | None -> (* a call to the self machine *) fprintf ff "self"
    | Some(o) -> fprintf ff "self.%a" name o in
  if !print_as_functions then fprintf ff "%a_%s %a" longname lname m instance i_opt
  else fprintf ff "%a.%s" instance i_opt m

and reset lname ff o =
  if !print_as_functions
  then fprintf ff "%a_reset self.%a" longname lname name o
  else fprintf ff "%a.reset()" name o

and left_value ff left =
  match left with
  | Oleft_name(n) -> name ff n
  | Oleft_record_access(left, n) ->
     fprintf ff "@[%a.%a@]" left_value left longname n
  | Oleft_index(left, idx) ->
     fprintf ff "@[%a.{%a}@]" left_value left (expression 0) idx

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
     fprintf ff "@[%a.(%a)@]" left_state_value left (expression 0) idx
  | Oleft_state_primitive_access(left, a) ->
     fprintf ff "@[%a.%a@]" left_state_value left access a

and assign ff left e =
  let arrow =
    match left with | Oleft_name _ -> ":=" | _ -> "<-" in
  fprintf ff "@[<v 2>%a %s %a@]" left_value left arrow (expression 2) e

and assign_state ff left e =
  fprintf ff "@[<v 2>%a <- %a@]" left_state_value left (expression 2) e

and access ff a =
  let s =
    match a with
    | Oderivative -> "der" | Ocontinuous -> "pos"
    | Ozero_out -> "zout"  | Ozero_in -> "zin" in
  fprintf ff "%s" s


and local ff n is_shared =
  fprintf ff "%s%a" (if is_shared then "!" else "") name n

and letvar ff n ty e_opt e =
  match e_opt with
    | None ->
        if !print_as_functions
        then fprintf ff "@[<v 0>let %a = ref (Obj.magic (): %a) in@ %a@]"
                name n Ptypes.output ty (expression 0) e
        else fprintf ff "@[<v 0>var %a: %a in@ %a@]"
                name n Ptypes.output ty (expression 0) e
    | Some(e0) ->
        if !print_as_functions
        then fprintf ff "@[<v 0>let %a = ref (%a:%a) in@ %a@]"
          name n (expression 0) e0 Ptypes.output ty (expression 0) e
        else fprintf ff "@[<v 0>var %a: %a = %a in@ %a@]"
          name n Ptypes.output ty (expression 0) e0 (expression 0) e

and expression prio ff e =
  let prio_e = priority e in
  if prio_e < prio then fprintf ff "(";
  begin match e.desc with
  | Oconst(i) -> immediate ff i
  | Oconstr0(lname) -> longname ff lname
  | Oconstr1(lname, e_list) ->
      fprintf ff "@[%a%a@]"
        longname lname (print_list_r (expression 1) "("","")") e_list
  | Oglobal(ln) -> longname ff ln
  | Olocal(n, sort) -> local ff n sort
  | Ostate(l) -> left_state_value ff l
  | Oindex(e, eidx) ->
      fprintf ff "%a.{@[%a@]}" (expression 1) e (expression 1) eidx
  | Otuple(e_list) ->
      fprintf ff "@[<hov2>%a@]" (print_list_r (expression 2) "("","")") e_list
  | Oapp(ln, []) ->
      fprintf ff "@[<hov2>%a ()@]" longname ln
  | Oapp(ln, e_list) ->
      fprintf ff "@[<hov2>%a %a@]"
        longname ln (print_list_r (expression 3) """""") e_list
  | Omethod(m, e_list) ->
      fprintf ff "@[<hov2>%a %a@]" method_call m
        (print_list_r (expression 3) """""") e_list
  | Orecord(r) ->
      print_record (print_couple longname (expression 4) """ =""") ff r
  | Orecord_access(e, lname) ->
      fprintf ff "%a.%a" (expression prio_e) e longname lname
  | Otypeconstraint(e, ty_e) ->
      fprintf ff "@[(%a : %a)@]" (expression prio_e) e ptype ty_e
  | Olet(pat_exp_list, e) ->
      fprintf ff "@[<v 0>%a@ %a@]"
        (print_list_l pat_exp "let ""and "" in") pat_exp_list
        (expression (prio_e-1)) e
  | Oletvar(x, ty, e_opt, e) ->
      letvar ff x ty e_opt e
  | Omatch(e, match_handler_l) ->
      fprintf ff "@[<v2>match %a with@ @[%a@]@]"
        (expression 0) e (print_list_l match_handler """""") match_handler_l
  | Oifthenelse(e, e1, e2) ->
      fprintf ff "@[<hv>if %a@ @[<hv 2>then@ %a@]@ @[<hv 2>else@ %a@]@]"
        (expression 0) e (expression prio_e) e1 (expression prio_e) e2
  | Ofor(is_to, n, e1, e2, e3) ->
      fprintf ff "@[<hv>for %a = %a %s %a@ @[<hv 2>do@ %a@ done@]@]"
        name n (expression 0) e1 (if is_to then "to" else "downto")
        (expression 0) e2 (expression 0) e3
  | Owhile(e1, e2) ->
      fprintf ff "@[<hv>while %a do %a done@]@]"
        (expression 0) e1 (expression 0) e2
  | Oassign(left, e) -> assign ff left e
  | Oassign_state(left, e) -> assign_state ff left e
  | Osequence(e1, e2) ->
      fprintf ff "@[<hv>@[%a@];@ @[%a@]@]"
              (expression (prio_e+2)) e1 (expression prio_e) e2
  end;
  if prio_e < prio then fprintf ff ")"

and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" pattern p (expression 0) e

and match_handler ff { w_pat = pat; w_body = b } =
  fprintf ff "@[<hov 4>| %a ->@ %a@]" pattern pat (expression 0) b

let expression ff e = expression 0 ff e

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

let print_memory ff (n, (m, ty, e_opt)) =
  let mem ff mem =
    match mem with
    | Discrete -> fprintf ff "disc"
    | Zero -> fprintf ff "zero"
    | Cont -> fprintf ff "cont" in
  match e_opt with
  | None -> fprintf ff "%a %a : %a" mem m name n Ptypes.output ty
  | Some(e) ->
       fprintf ff "%a %a : %a = %a" mem m name n Ptypes.output ty expression e

let print_name_with_type ff (n, ty) =
  fprintf ff "%a : %a" name n Ptypes.output ty

let one_instance ff (n, ln, k) =
  fprintf ff "@[%a : %s(%a)@]" name n (kind k) longname ln

let one_method ff { m_name = m_name; m_param = p_list; m_body = e } =
  fprintf ff "@[<hov 2>method %s %a =@ %a@]"
    (method_name m_name) pattern_list p_list expression e

(** Define the data-type for the internal state of a machine *)
let def_type_for_a_machine ff f memories instances =
  let one_entry ff (n, m) =
    fprintf ff "@[mutable %a : '%s@]" name n m in
  let i, params, entries =
    List.fold_right
      (fun (n, _) (i, params, entries) ->
        let m = Misc.int_to_alpha i in (i+1, m :: params, (n, m) :: entries))
      memories (0, [], []) in
  let i, params, entries =
    List.fold_right
      (fun (n, _, _) (i, params, entries) ->
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

let def_cont_type ff =
  fprintf ff
          "@[type continuous = { mutable pos: float; mutable der: float }@.@]"

let def_zero_crossing_type ff =
  fprintf ff
          "@[type zerocrossing = { mutable zin: bool; mutable zout: float }@.@]"

let def_signal_type ff =
  fprintf ff
          "@[type 'a signal = 'a * bool@.\
             type zero = bool@.@]"

(** Define the method *)
let def_method_as_a_function f ff
    { m_name = m_name; m_param = pat_list; m_body = e } =
  fprintf ff "@[<v 2>let %s_%s self %a =@ %a@.@.@]"
    f (method_name m_name) pattern_list pat_list expression e

(** Define the method *)
let def_method_as_a_function_name f ff { m_name = m_name } =
  fprintf ff "%s_%s" f (method_name m_name)

(** Define the allocation function *)
let def_alloc_for_a_machine ff f memories instances =
  let one_memory ff (n, (m, ty, e_opt)) =
    match m with
    | Zero -> fprintf ff "%a = { zin = false; zout = 1.0 }" name n
    | Cont ->
      begin match e_opt with
        | None -> fprintf ff "%a = { pos = 0.0; der = 0.0 }" name n
        | Some(e) -> fprintf ff "%a = { pos = %a; der = 0.0 }" name n expression e
      end
    | Discrete ->
      begin match e_opt with
        | None ->
          fprintf ff "@[%a = (Obj.magic (): %a)@]" name n Ptypes.output ty
        | Some(e) ->
          fprintf ff "@[%a = (%a: %a)@]" name n expression e Ptypes.output ty
        end in
  let one_instance ff (n, ln, k) =
    fprintf ff "@[%a = %a_alloc () (* %s *) @]" name n longname ln (kind k)  in
  if memories = []
  then if instances = []
       then fprintf ff "@[let %s_alloc () = ()@.@.@]" f
       else
         fprintf ff "@[<v 2>let %s_alloc () =@ { @[%a@] }@.@.@]"
                 f (print_list_r one_instance """;""") instances
  else if instances = []
  then
    fprintf ff "@[<v 2>let %s_alloc () =@ { @[%a@] }@.@.@]"
            f (print_list_r one_memory """;""") memories
  else
    fprintf ff "@[<v 2>let %s_alloc () =@ { @[%a%a@] }@.@.@]"
            f
            (print_list_r one_memory """;"";") memories
            (print_list_r one_instance """;""") instances

(** Print a machine *)
let machine_as_a_class ff f { m_kind = k;
                              m_memories = memories;
                              m_instances = instances;
                              m_methods = m_list } =
  fprintf ff "@[<hov 2>let %s = machine(%s) {@,\
                  @[@[<v 2>memories @[%a@]@]@;\
                  @[@[<v 2>instances @[%a@]@]@;\
                  @[%a@]}@.@]@.@]@]"
    f
    (kind k)
    (print_list_r_empty print_memory """;""") memories
    (print_list_r_empty one_instance """;""") instances
    (print_list_r one_method """""") m_list

(** Represent a machine as a record of functions *)
(* order methods in this order: *)
(* alloc < maxsize < derivatives < step < crossings < reset *)
let order m1 m2 =
  let int { m_name = m_name } =
    match m_name with
      | Omaxsize -> 1 | Oderivatives -> 2
      | Ostep -> 3 | Ocrossings -> 4 | Oreset -> 5
      | Ocin -> 6 | Ocout -> 7 | Odout -> 8
      | Ozin -> 9 | Ozout -> 10 | _ -> 0 in
  Pervasives.compare (int m1) (int m2)

let tuple ff f k m_list =
  match k with
    | Deftypes.Tany -> ()
    | Deftypes.Tdiscrete _ | Deftypes.Tcont ->
        let m_list = List.sort order m_list in
        fprintf ff
          "@[<hov 2>let %s = %s_alloc, %a@.@]" f f
          (print_list_r (def_method_as_a_function_name f) """,""") m_list

(** Print a machine as pieces with a type definition for the state *)
(** an a collection of functions *)
let machine_as_functions ff f { m_kind = k;
                                m_memories = memories;
                                m_instances = instances;
                                m_methods = m_list } =
  def_type_for_a_machine
    ff f memories instances;
  def_alloc_for_a_machine
    ff f memories instances;
  (print_list_r (def_method_as_a_function f) """""") ff m_list;
  tuple ff f k m_list

let machine ff f m =
  if !print_as_functions then machine_as_functions ff f m
  else machine_as_a_class ff f m


let implementation ff impl = match impl.desc with
  | Oletvalue(n, e) ->
      fprintf ff "@[<v 2>let %a = %a@.@.@]" shortname n expression e
  | Oletfun(n, pat_list, e) ->
      fprintf ff "@[<v 2>let %a %a =@ %a@.@.@]"
        shortname n pattern_list pat_list expression e
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
  if !print_as_functions
  then begin def_cont_type ff; def_zero_crossing_type ff; def_signal_type ff end;
  List.iter (implementation ff) impl_list
