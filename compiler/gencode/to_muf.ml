open Location
open Ident
open Obc
open Muf_compiler_libs.Ast

exception Not_yet_implemented of string

let not_yet_implemented msg =
  raise (Not_yet_implemented msg)

let immediate c =
  begin match c with
  | Oint i -> Cint i
  | Oint32 i -> Cint 32
  | Ofloat f -> Cfloat (string_of_float f)
  | Obool b -> Cbool b
  | Ostring s -> Cstring s
  | Ochar c -> Cchar c
  | Ovoid -> Cunit
  | Oany -> Cany
  end

let ident_name n = Ident.name n
let ident n = { name = ident_name n }

let lident_name n =
  match n with
  | Lident.Name n -> n
  | Modname n -> n.qual ^ "_" ^ n.id

let lident n = { name = lident_name n }

let rec pattern patt =
  { patt = pattern_desc patt; pmeta = ()}

and pattern_desc pat =
  begin match pat with
  | Owildpat -> Pany
  | Oconstpat(_) -> Pany
  | Oconstr0pat(_) -> Pany
  | Oconstr1pat(_, _x) -> Pany
  | Ovarpat(n, _ty_exp) -> Pid (ident n)
  | Otuplepat(pat_list) -> Ptuple (List.map pattern pat_list)
  | Oaliaspat(_p, _n) -> not_yet_implemented "pat alias"
  | Oorpat(_pat1, _pat2) -> not_yet_implemented "or pat"
  | Otypeconstraintpat(_p, _ty_exp) -> not_yet_implemented "pat contraint"
  | Orecordpat(_n_pat_list) -> not_yet_implemented "record pat"
  end

let rec expression e =
  { expr = expression_desc e; emeta = (); }

and expression_desc e =
  begin match e with
  | Oconst c -> Econst (immediate c)
  | Oconstr0(lname) -> Econst (immediate (Ostring (lident_name lname)))
  | Oconstr1(lname, e_list) ->
      not_yet_implemented ("expression: constr1("^(lident_name lname)^")")
  | Oglobal(ln) -> Evar (lident ln)
  | Olocal(n) -> Evar (ident n)
  | Ovar(_is_mutable, n) -> Evar (ident n)
  | Ostate(l) -> left_state_value l
  | Oaccess(e, eidx) -> not_yet_implemented "expression: access"
  | Ovec(e, se) -> not_yet_implemented "expression: vec"
  | Oupdate(se, e1, i, e2) -> not_yet_implemented "expression: update"
  | Oslice(e, s1, s2) -> not_yet_implemented "expression: slice"
  | Oconcat(e1, s1, e2, s2) -> not_yet_implemented "expression: concat"
  | Otuple(e_list) -> Etuple (List.map expression e_list)
  | Oapp(e, e_list) ->
      let args =
        match List.map expression e_list with
        | [] -> { expr = Etuple []; emeta = (); }
        | [e] -> e
        | args -> { expr = Etuple args; emeta = () }
      in
      Eapp (expression e, args)
  | Omethodcall m -> method_call m
  | Orecord(r) ->
      Erecord (List.map (fun (x, e) -> ((lident_name x), expression e)) r)
  | Orecord_access(e_record, lname) ->
      Efield (expression e_record, lident_name lname)
  | Orecord_with(e_record, r) -> not_yet_implemented "expression: record_with"
  | Otypeconstraint(e, ty_e) ->
      not_yet_implemented "expression: type constraint"
  | Oifthenelse(e, e1, e2) ->
      Eif (expression e, expression e1, expression e2)
  | Oinst(i) -> (* inst i *) assert false (* XXX TODO XXX *)
  end

and left_state_value left =
  assert false (* XXX TODO XXX *)
  (* match left with *)
  (* | Oself -> fprintf ff "self." *)
  (* | Oleft_instance_name(n) -> fprintf ff "self.%a" name n *)
  (* | Oleft_state_global(ln) -> longname ff ln *)
  (* | Oleft_state_name(n) -> fprintf ff "self.%a" name n *)
  (* | Oleft_state_record_access(left, n) -> *)
  (*    fprintf ff "@[%a.%a@]" left_state_value left longname n *)
  (* | Oleft_state_index(left, idx) -> *)
  (*    fprintf ff "@[%a.(%a)@]" left_state_value left (exp 0) idx *)
  (* | Oleft_state_primitive_access(left, a) -> *)
  (*    fprintf ff "@[%a.%a@]" left_state_value left access a *)

and method_call m =
  let method_name =
    match m.met_machine with
    | Some name -> lident name
    | None -> not_yet_implemented "method_call: unkown machine"
  in
  let static_args =
    match m.met_instance with
    | None -> []
    | Some (_, e_list) -> List.map expression e_list
  in
  let inputs = List.map expression m.met_args in
  let args =
    match static_args @ inputs with
    | [] -> { expr = Etuple []; emeta = (); }
    | [e] -> e
    | args -> { expr = Etuple args; emeta = (); }
  in
  Eapp ({ expr = Evar method_name; emeta = (); }, args)

and inst updated updated i k =
  { expr = inst_desc updated i k; emeta = (); }

and inst_desc updated i k =
  assert false (* XXX TODO XXX *)
 (*  begin match i with *)
 (*  | Olet(p, e, i) -> Elet (pattern p, expression e, inst i k) *)
 (*  | Oletvar(x, is_mutable, ty, e_opt, i) -> letvar ff x is_mutable ty e_opt i *)
 (*  | Omatch(e, match_handler_l) -> *)
 (*      fprintf ff "@[<v2>begin @[match %a with@ @[%a@]@] end@]" *)
 (*        (exp 0) e *)
 (* (print_list_l match_handler """""") match_handler_l *)
 (*  | Ofor(is_to, n, e1, e2, i3) -> *)
 (*       fprintf ff "@[<hv>for %a = %a %s %a@ @[<hv 2>do@ %a@ done@]@]" *)
 (*               name n (exp 0) e1 (if is_to then "to" else "downto") *)
 (*               (exp 0) e2 (inst 0) i3 *)
 (*    | Owhile(e1, i2) -> *)
 (*       fprintf ff "@[<hv>while %a do %a done@]@]" *)
 (*               (exp 0) e1 (inst 0) i2 *)
 (*    | Oassign(left, e) -> assign ff left e *)
 (*    | Oassign_state(left, e) -> assign_state ff left e *)
 (*    | Osequence(i_list) -> *)
 (*       if i_list = [] *)
 (*       then fprintf ff "()" *)
 (*       else fprintf *)
 (*              ff "@[<hv>%a@]" (print_list_r (inst (prio_i + 1)) "" ";" "") i_list *)
 (*    | Oexp(e) -> exp prio ff e *)
 (*    | Oif(e, i1, None) -> *)
 (*       fprintf ff "@[<hov>if %a@ then@ %a@]" (exp 0) e sinst i1 *)
 (*    | Oif(e, i1, Some(i2)) -> *)
 (*       fprintf ff "@[<hov>if %a@ then@ %a@ else %a@]" *)
 (*               (exp 0) e sinst i1 sinst i2 *)
 (*  end; *)
