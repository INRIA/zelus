(* Print Python code *)

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
  | Obool b -> if b then fprintf ff "True" else fprintf ff "False"
  | Ostring s -> fprintf ff "%S" s
  | Ochar c -> fprintf ff "'%c'" c
  | Ovoid -> pp_print_string ff "()"
  | Oany -> fprintf ff "None"


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
  | Oconstr0pat(lname) -> fprintf ff "\"%a\"" longname lname
  | Oconstr1pat(lname, pat_list) ->
      fprintf ff "@[%a%a@]"
        longname lname (print_list_r pattern "("","")") pat_list
  | Ovarpat(n, ty_exp) ->
      fprintf ff "%a" name n
  | Otuplepat(pat_list) ->
      pattern_list ff pat_list
  | Oaliaspat(p, n) -> fprintf ff "@[%a as %a@]" pattern p name n
  | Oorpat(pat1, pat2) -> fprintf ff "@[%a | %a@]" pattern pat1 pattern pat2
  | Otypeconstraintpat(p, ty_exp) ->
      fprintf ff "%a" pattern p
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
    | None -> fprintf ff "self" | Some(o, _) -> fprintf ff "self.%a" name o in
  let instance ff i_opt =
    match i_opt with
    | None -> (* a call to the self machine *) fprintf ff "self"
    | Some(o, e_list) ->
        match e_list with
        | [] -> fprintf ff ""
        | e_list ->
            assert false;
            fprintf ff "self.%a(%a)" name o
              (print_list_no_space
                 (print_with_braces (exp 3) "[" "]") "" "" "")
              e_list in
  fprintf ff "%a.%s(%a%a)"
    instance_name i_opt m instance i_opt
    (print_list_r (exp 3) "" "," "") e_list

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
      fprintf ff "%a = %a" name n (exp 2) e
  | _ ->
      fprintf ff "%a = %a" left_value left (exp 2) e

and assign_state ff left e =
  match left with
  | Oleft_state_global(gname) ->
      fprintf ff "%a = %a" longname gname (exp 2) e
  | _ -> fprintf ff "%a = %a" left_state_value left (exp 2) e

and letvar ff n is_mutable ty e_opt i =
  let s = "" in
  match e_opt with
  | None ->
      fprintf ff "@[<v 0>%a = %s@]@[<v 0>%a@]"
        name n s (inst 0 false) i
  | Some(e0) ->
      fprintf ff "@[<v 0>%a = %s(%a)@]@[<v 0>%a@]"
        name n s (exp 0) e0 (inst 0 false) i

and exp prio ff e =
  let prio_e = priority_exp e in
  (* if prio_e < prio then fprintf ff "("; *)
  begin match e with
    | Oconst(i) -> immediate ff i
    | Oconstr0(lname) -> fprintf ff "\"%a\"" longname lname
    | Oconstr1(lname, e_list) ->
        assert false;
        fprintf ff "@[%a%a@]"
          longname lname (print_list_r (exp prio_e) "("","")") e_list
    | Oglobal(ln) -> begin match ln with 
      | Modname {id = ("+" | "+."); qual = "Stdlib"} -> fprintf ff "add"
      | Modname {id = ("-" | "-."); qual = "Stdlib"} -> fprintf ff "sub"
      | Modname {id = ("*" | "*."); qual = "Stdlib"} -> fprintf ff "mul"
      | Modname {id = "/" ; qual = "Stdlib"} -> fprintf ff "floordiv"
      | Modname {id = "/." ; qual = "Stdlib"} -> fprintf ff "truediv"
      | Modname {id = ">" ; qual = "Stdlib"} -> fprintf ff "gt"
      | Modname {id = ">=" ; qual = "Stdlib"} -> fprintf ff "ge"
      | Modname {id = "<" ; qual = "Stdlib"} -> fprintf ff "lt"
      | Modname {id = "<=" ; qual = "Stdlib"} -> fprintf ff "le"
      | Modname {id = "=" ; qual = "Stdlib"} -> fprintf ff "eq"      
      | _ -> longname ff ln end 
    | Olocal(n) -> local ff n
    | Ovar(is_mutable, n) ->
        fprintf ff "%a" local n
    | Ostate(l) -> left_state_value ff l
    | Oaccess(e, eidx) ->
        fprintf ff "%a[%a]" (exp prio_e) e (exp prio_e) eidx
    | Ovec(e, se) ->
        assert false;
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
        assert false;
        (* returns a fresh vector [_t] of size [se] equal to [e2] except at *)
        (* [i] where it is equal to [e2] *)
        fprintf ff "@[(let _t = Array.copy (%a) in@ _t.(%a) <- %a; _t)@]"
          (exp 0) e1 (exp 0) i (exp 0) e2
    | Oslice(e, s1, s2) ->
        assert false;
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
        assert false;
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
        fprintf ff "%a" (print_list_r (exp prio_e) """,""") e_list
    | Oapp(e, e_list) ->
        fprintf ff "%a(%a)"
          (exp (prio_e + 1)) e (print_list_r (exp (prio_e + 1)) """,""") e_list
    | Omethodcall m -> method_call ff m
    | Orecord(r) ->
        print_record (print_couple longname (exp prio_e) """ =""") ff r
    | Orecord_access(e_record, lname) ->
        fprintf ff "%a[%a]" (exp prio_e) e_record longname lname
    | Orecord_with(e_record, r) ->
        assert false;
        fprintf ff "@[{ %a with %a }@]"
          (exp prio_e) e_record
          (pp_print_list ~pp_sep:pp_print_cut  (print_couple longname (exp prio_e) """ =""")) r
    | Otypeconstraint(e, ty_e) -> ()
    | Oifthenelse(e, e1, e2) ->
        fprintf ff "%a if %a else %a"
          (exp prio_e) e1 (exp 0) e (exp prio_e) e2
    | Oinst(i) -> inst prio false ff i
  end
  (* if prio_e < prio then fprintf ff ")" *)

and inst prio r ff i =
  let prio_i = priority_inst i in
  if prio_i < prio then fprintf ff "";
  begin
    match i with
    | Olet(p, e, i) ->
        fprintf ff "@[<v 0>%a@,%a@]" pat_exp (p, e) (inst (prio_i-1) r) i
    | Oletvar(x, is_mutable, ty, e_opt, i) -> letvar ff x is_mutable ty e_opt i
    | Omatch(e, [{w_pat = Owildpat; w_body}]) -> (inst 0 false) ff w_body
    | Omatch(e, match_handler_l) -> 
          fprintf ff "@[<v>@[<v 4>%a@]" 
          (pp_print_list ~pp_sep:(fun ff () -> fprintf ff "@,@[<v 4>el") (match_handler e)) match_handler_l
    | Ofor(is_to, n, e1, e2, i3) ->
        fprintf ff "@[<v 4>for %a in range(%a, %a, %d):@,%a@]"
          name n 
          (exp 0) e1 
          (exp 0) e2 
          (if is_to then 1 else -1) 
          (inst 0 false) i3
    | Owhile(e1, i2) ->
        fprintf ff "@[<v 4>while %a:%a@]"
          (exp 0) e1 (inst 0 false) i2
    | Oassign(left, e) -> assign ff left e
    | Oassign_state(left, e) -> assign_state ff left e
    | Osequence(i_list) -> sinst r ff i
    | Oexp(e) -> begin match r with
        | true -> fprintf ff "return %a" (exp prio) e
        | false -> fprintf ff "%a" (exp prio) e
      end
    | Oif(e, i1, None) ->
        fprintf ff "@[<v 4>if %a:@,%a@]" (exp 0) e (sinst r) i1
    | Oif(e, i1, Some(i2)) ->
        fprintf ff "@[<v 0>@[<v 4>if %a:@,%a@]@,@[<v 4>else:@,%a@]@]"
          (exp 0) e (sinst r) i1 (sinst r) i2
  end;
  if prio_i < prio then fprintf ff ""

(* special treatment to add an extra parenthesis if [i] is a sequence *)
and sinst r ff i =
  match i with
  | Osequence(i_list) ->
      begin match List.rev(i_list) with
        | [] -> fprintf ff "pass"
        | [i] -> fprintf ff "%a" (inst 0 r) i
        | fi::ri_list -> 
            fprintf ff "@[<v>%a@,%a@]" 
              (pp_print_list ~pp_sep:pp_print_cut (inst 0 false)) 
              (List.rev ri_list) 
              (inst 0 r) fi
      end
  | _ -> inst 0 r ff i

and pat_exp ff (p, e) =
  fprintf ff "@[@[%a@] =@ @[%a@]@]" pattern p (exp 0) e

and exp_with_typ ff (e, ty) =
  fprintf ff "%a" (exp 2) e

and match_handler e ff { w_pat = pat; w_body = b } =
  match pat with
  | Owildpat -> fprintf ff "se:@,%a@]" (inst 0 false) b (* else case *)
  | _ -> fprintf ff "if %a == %a:@,%a@]" (exp 0) e pattern pat (inst 0 false) b (* if/elif case *)


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
(* let def_type_for_a_machine ff f memories instances =
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
      (print_list_r one_entry """;""") entries *)


(** Print the method as a function *)
let pmethod f ff { me_name = me_name; me_params = pat_list;
                   me_body = i; me_typ = ty } =
  fprintf ff "@[<v 4>def %s (self, %a):@,%a@,@]"
    (method_name me_name) pattern_list pat_list (inst 2 true) i

(* create an array of type t[n_1]...[n_k] *)
let array_make print arg ff ie_size =
  let rec array_rec ff = function
    | [] -> fprintf ff "%a" print arg
    | ie :: ie_size ->
        assert false;
        fprintf ff "@[<hov>Array.init %a@ (fun _ -> %a)@]"
          (exp 3) ie array_rec ie_size in
  array_rec ff ie_size

let rec array_of e_opt ty ff ie_size =
  assert false;
  let exp_of ff (e_opt, ty) =
    match e_opt, ty with
    | Some(e), _ -> exp 2 ff e
    | _ -> fprintf ff "None" in
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
  | None -> fprintf ff "pass" | Some(i) -> fprintf ff "%a" (inst 0 false) i

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
              fprintf ff "@[self.%a = %a@]" name n
                (array_make (fun ff _ -> fprintf ff "None") ())
                m_size
          | Some(e) ->
              fprintf ff "@[self.%a = %a@]" name n
                (array_make exp_with_typ (e, ty)) m_size
        end
    | Some(m) ->
        match m with
        | Deftypes.Zero ->
            fprintf ff "@[%a = @[<hov 2>{ \"zin\": %a; \"zout\" = %a }@]@]"
              name n (array_of e_opt Initial.typ_bool) m_size
              (array_of (Some(Oconst(Ofloat(1.0)))) Initial.typ_float)
              m_size
        | Deftypes.Cont ->
            fprintf ff "@[%a = @[<hov 2>{ \"pos\": %a; \"der\": %a }@]@]"
              name n (array_of e_opt ty) m_size
              (* the default value of a derivative must be zero *)
              (array_of (Some(Oconst(Ofloat(0.0)))) ty) m_size
        | Deftypes.Horizon | Deftypes.Period
        | Deftypes.Encore | Deftypes.Major ->
            fprintf ff "self.%a = %a" name n (array_of e_opt ty) m_size in

  let print_instance ff { i_name = n; i_machine = ei;
                          i_kind = k; i_params = e_list; i_size = ie_size } =
    fprintf ff "@[self.%a = %a @]" name n
      (array_make (fun ff n -> fprintf ff "%a ()" (exp 0) ei) n)
      ie_size   in
  if memories = []
  then if instances = []
    then fprintf ff "@[<v 4>def __init__ (self):@,%a@,@]" print_initialize i_opt
    else
      fprintf ff "@[<v 4>def __init__ (self):@,%a@,%a@,@]"
        print_initialize i_opt
        (pp_print_list ~pp_sep:pp_print_cut print_instance) instances
  else if instances = []
  then
    fprintf ff "@[<v 4>def __init__ (self):@,%a@,%a@,@]"
      print_initialize i_opt (pp_print_list ~pp_sep:pp_print_cut print_memory) memories
  else
    fprintf ff "@[<v 4>def __init__ (self):@,%a@,%a@,%a@,@]"
      print_initialize i_opt
      (pp_print_list ~pp_sep:pp_print_cut print_memory) memories
      (pp_print_list ~pp_sep:pp_print_cut print_instance) instances

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
          assert false;
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
        fprintf ff "dest.%a = %a" name n
          (array_copy (fun ff _ -> fprintf ff "self.%a" name n)) m_size
    | Some(m) ->
        match m with
        | Deftypes.Zero ->
            fprintf ff "@[<v>dest.%a.zin = %a@,dest.%a.zout = %a@]"
              name n
              (array_copy (fun ff _ -> fprintf ff "source.%a.zin" name n))
              m_size
              name n
              (array_copy (fun ff _ -> fprintf ff "source.%a.zout" name n))
              m_size
        | Deftypes.Cont ->
            fprintf ff "@[<v>dest.%a.pos = %a@,dest.%a.der = %a@]"
              name n
              (array_copy (fun ff _ -> fprintf ff "source.%a.pos" name n))
              m_size
              name n
              (array_copy (fun ff _ -> fprintf ff "source.%a.der" name n))
              m_size
        | Deftypes.Horizon | Deftypes.Period
        | Deftypes.Encore | Deftypes.Major ->
            fprintf ff "@[dest.%a = self.%a@]" name n name n in
  let copy_instance ff { i_name = n; i_machine = ei;
                         i_kind = k; i_params = e_list; i_size = ie_size } =
    fprintf ff "@[%a # %s@]"
      (array_make
         (fun ff n ->
            fprintf ff "@[self.%a.copy(dest.%a)@]" name n name n)
         n)
      ie_size (kind k)  in
  if memories = []
  then if instances = []
    then fprintf ff "@[<v 4> def copy(self, dest):@,pass@,@]"
    else
      fprintf ff "@[<v 4>def copy(self, dest):@,%a@,@]"
        (pp_print_list ~pp_sep:pp_print_cut copy_instance) instances
  else if instances = []
  then
    fprintf ff "@[<v 4>def copy(self, dest):@,%a@,@]"
      (pp_print_list ~pp_sep:pp_print_cut copy_memory) memories
  else
    fprintf ff "@[<v 4>def copy(self, dest):@,%a@,%a@,@]"
      (pp_print_list ~pp_sep:pp_print_cut copy_memory) memories
      (pp_print_list ~pp_sep:pp_print_cut copy_instance) instances

(** Print a machine as pieces with a type definition for the state *)
(** and a collection of functions *)
let machine f ff { ma_kind = k;
                   ma_params = pat_list;
                   ma_initialize = i_opt;
                   ma_memories = memories;
                   ma_instances = instances;
                   ma_methods = m_list } =
  (* print the code for [f] *)
  List.iter (fun p -> fprintf ff "@[<v 4>def %s(%a):@," f pattern p) pat_list;
  fprintf ff "@[<v 4>class %s(Node):@," f;
  if !Misc.with_copy then
    fprintf ff
      "@[<v>%a@,%a@,%a@]"
      (palloc f i_opt memories) instances
      (pcopy f memories) instances
      (print_list_r (pmethod f) """""") m_list
  else
    fprintf ff "@[<v>%a@,%a@]@]"
      (palloc f i_opt memories) instances
      (pp_print_list ~pp_sep:pp_print_cut (pmethod f)) m_list;
  fprintf ff "@."

let implementation ff impl = match impl with
  | Oletvalue(n, i) ->
      fprintf ff "@[<v>@[<v 4>def %a ():@,%a@]@,%a = %a()@,@,@]@." shortname n (inst 0 true) i shortname n shortname n
  | Oletfun(n, pat_list, i) ->
      fprintf ff "@[<v>@[<v 4>def %a %a:@,%a@]@,@,@]@."
        shortname n pattern_list pat_list (inst 0 true) i
  | Oletmachine(n, m) -> machine n ff m
  | Oopen(s) -> fprintf ff "@[from %s import *@]@." s
  | Otypedecl(l) -> ()
  (* fprintf ff "@[%a@.@]"
  (print_list_l
     (fun ff (s, s_list, ty_decl) ->
       fprintf ff "%a%s =@ %a"
               Ptypes.print_type_params s_list
               s type_decl ty_decl)
     "type ""and """)
  l *)

let implementation_list ff impl_list =
  (* fprintf ff "@[\"\"\" %s \"\"\"@]" header_in_file; *)
  (* fprintf ff "@[open Ztypes@.@]"; *)
  fprintf ff "from operator import *@.";
  fprintf ff "from pyzls import Node@.@.";
  List.iter (implementation ff) impl_list;
  fprintf ff "@."
