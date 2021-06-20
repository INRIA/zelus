(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the printer *)

open Location
open Misc
open Zelus
open Deftypes
open Ptypes
open Global
open Modules
open Pp_tools
open Format

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

let qualident ff { Lident.qual = m; Lident.id = s } =
  fprintf ff "%s.%s" m (parenthesis s)

let longname ff ln =
  let ln = Initial.short (currentname ln) in
  match ln with
    | Lident.Name(m) -> shortname ff m
    | Lident.Modname(qual) -> qualident ff qual

let name ff n = shortname ff (Ident.name n)

let source_name ff n = shortname ff (Ident.source n)

let immediate ff = function
  | Eint i -> fprintf ff "%d" i
  | Efloat f -> fprintf ff "%f" f
  | Ebool b -> if b then fprintf ff "true" else fprintf ff "false"
  | Estring s -> fprintf ff "%S" s
  | Echar c -> fprintf ff "'%c'" c
  | Evoid -> fprintf ff "()"

let rec ptype ff { desc } =
  match desc with
  | Etypevar(s) -> fprintf ff "'%s" s
  | Etypeconstr(ln, ty_list) ->
     fprintf ff "@[<hov2>%a@]%a"
       (print_list_r_empty ptype "("","")") ty_list
       longname ln
  | Etypetuple(ty_list) ->
     fprintf ff "@[<hov2>%a@]" (print_list_r ptype "(""*"")") ty_list
  | Etypefun(k, ty_arg, ty_res) ->
     let s = match k with | Kfun -> "->" | Knode -> "=>" | Kstatic -> ">" in
     fprintf ff "@[<hov2>%a %s %a@]" ptype ty_arg s ptype ty_res

let rec pattern ff { pat_desc } =
  match pat_desc with
  | Evarpat(n) -> fprintf ff "%a" name n
  | Ewildpat -> fprintf ff "_"
  | Econstpat(im) -> immediate ff im
  | Econstr0pat(ln) -> longname ff ln
  | Econstr1pat(ln, pat_list) ->
     fprintf ff "@[%a%a@]" longname ln (pattern_list "(" "," ")") pat_list
  | Etuplepat(pat_list) -> pattern_list "(" "," ")" ff pat_list
  | Etypeconstraintpat(p, ty_exp) ->
     fprintf ff "@[(%a:%a)@]" pattern p ptype ty_exp
  | Erecordpat(n_pat_list) ->
     print_record (print_couple longname pattern """ =""") ff n_pat_list
  | Ealiaspat(p, n) ->
     fprintf ff "%a as %a" pattern p name n
  | Eorpat(pat1, pat2) ->
     fprintf ff "%a | %a" pattern pat1 pattern pat2

and pattern_list po sep pf ff pat_list =
  fprintf ff "@[%a@]" (print_list_r pattern po sep pf) pat_list

let init exp ff e_opt =
  match e_opt with | None -> () | Some(e) -> fprintf ff " init %a" exp e
let default exp ff e_opt =
  match e_opt with | None -> () | Some(e) -> fprintf ff " default %a" exp e
  
let print_vardec_list exp ff vardec_list =
  let vardec ff
      { var_name = x; var_default = d_opt; var_init = i_opt } =
    fprintf ff "@[%a%a%a@]" 
      name x (default exp) d_opt (init exp) i_opt in
  if vardec_list <> []
  then fprintf ff "@[<v 2>%a@ @]"
    (print_list_r vardec "local " "," "") vardec_list

let skind ff k =
  let s = match k with
  | Cont -> "cont" | Zero -> "zero" | Discrete -> "reg" in
  fprintf ff "%s" s

let tkind ff k =
  match k with
  | Tstatic -> fprintf ff "S"
  | Tfun -> fprintf ff "F"
  | Tnode -> fprintf ff "N"

let print_binding ff (n, { t_sort; t_typ }) =
  match t_sort with
  | Sstatic -> fprintf ff "@[static %a: %a@,@]" name n Ptypes.output t_typ
  | Sval -> fprintf ff "@[val %a: %a@,@]" name n Ptypes.output t_typ
  | Svar ->
     fprintf ff "@[var %a: %a@,@]" name n Ptypes.output t_typ
  | Smem { m_kind } ->
       fprintf ff "@[%a %a: %a@,@]"
         skind m_kind name n Ptypes.output t_typ

let print_env ff env =
  if !vverbose then begin
    let env = Ident.Env.bindings env in
    if env <> [] then
      fprintf ff "@[<v 0>(* defs: %a *)@,@]"
        (print_list_r print_binding """;""") env
  end

let print_writes ff { dv ; di; der } =
  if !vverbose then begin
    let dv = Ident.S.elements dv in
    let di = Ident.S.elements di in
    let der = Ident.S.elements der in
    open_box 0;
    if dv <> [] then
      fprintf ff
  	    "@[<v 0>(* dv = {@[%a@]} *)@ @]" (print_list_r name "" "," "") dv;
    if di <> [] then
      fprintf ff
  	    "@[<v 0>(* di = {@[%a@]} *)@ @]" (print_list_r name "" "," "") di;
    if der <> [] then
      fprintf ff
  	    "@[<v 0>(* der = {@[%a@]} *)@ @]" (print_list_r name "" "," "") der;
    close_box ()
  end

let print_eq_info ff { eq_write } =
  print_writes ff eq_write

(* print a block *)
let block exp body ff { b_vars; b_body; b_write; b_env } =
  fprintf ff "@[<hov 0>@[%a@]@[%a@]@[%a@]@[%a@]@]"
    (print_vardec_list exp) b_vars
    print_writes b_write
    print_env b_env
    body b_body

let match_handler body ff { m_pat; m_body; m_env; m_reset; m_zero } =
  fprintf ff "@[<hov 4>| %a -> %s%s@,%a%a@]"
    pattern m_pat (if m_reset then "(* reset *)" else "")
                (if m_zero then "(* zero *)" else "")
    print_env m_env body m_body

let present_handler scondpat body ff { p_cond; p_body; p_env } =
  fprintf ff "@[<hov4>| (%a) ->@ @[<v 0>%a%a@]@]"
    scondpat p_cond print_env p_env body p_body

let scondpat expression ff scpat =
  let rec scondpat ff scpat = match scpat.desc with
    | Econdand(scpat1, scpat2) ->
       fprintf ff "@[%a &@ %a@]" scondpat scpat1 scondpat scpat2
    | Econdor(scpat1, scpat2) ->
       fprintf ff "@[%a |@ %a@]" scondpat scpat1 scondpat scpat2
    | Econdexp(e) -> expression ff e
    | Econdpat(e, pat) -> fprintf ff "%a(%a)" expression e pattern pat
    | Econdon(scpat1, e) ->
       fprintf ff "@[%a on@ %a@]" scondpat scpat1 expression e in
  scondpat ff scpat

  (*
let automaton_handler_list
      is_weak body body_in_escape expression ff s_h_list e_opt =
  let statepat ff spat = match spat.desc with
    | Estate0pat(n) -> name ff n
    | Estate1pat(n, n_list) ->
       fprintf ff "%a%a" name n (print_list_r name "("","")") n_list in
  
  let rec state ff se = match se.desc with
    | Estate0(n) -> name ff n
    | Estate1(n, e_list) ->
       fprintf ff "%a%a" name n (print_list_r expression "("","")") e_list
  | Estateif(e, se1, se2) ->
       fprintf ff "@[if %a@,then %a@,else %a@]"
                   expression e state se1 state se2 in
  
  let automaton_handler is_weak body body_in_escape expression ff
        { s_state = s; s_body = b; s_trans = t_list; s_env = env } =
    
    let escape ff { e_cond = scpat; e_reset = r; e_body = b_opt;
		    e_next_state = ns; e_env = env } =
      match b_opt with
      | None ->
         fprintf ff "@[<v4>| %a %a%s@ %a@]"
           (scondpat expression) scpat print_env env
           (if r then "then" else "continue") state ns
      | Some(b) ->
         fprintf ff "@[<v4>| %a %a%s@ %a in %a@]"
           (scondpat expression) scpat print_env env
           (if r then "then" else "continue")
           body_in_escape b state ns in
    
    let escape_list ff t_list =
      if t_list = [] then fprintf ff "done"
      else
        print_list_r escape
	  (if is_weak then "until " else "unless ") "" "" ff t_list in
    fprintf ff "@[<v 4>| %a ->@ %a@[<v>%a@,%a@]@]"
      statepat s print_env env body b escape_list t_list in
  
  let automaton_handler_list ff s_h_list =
    print_list_l
      (automaton_handler is_weak body body_in_escape expression)
      """"""
      ff s_h_list in

    fprintf ff "@[<hov0>automaton%s@ @[%a@]@,%a@]"
	 (if is_weak then "(* weak *)" else "(* strong *)")
	 automaton_handler_list s_h_list
	 (print_opt (print_with_braces state " init" "")) e_opt

let rec expression ff e =
  if Deftypes.is_no_typ e.e_typ && !vverbose then
    fprintf ff "@[(* %a *)@]" Ptypes.output e.e_typ;
  match e.e_desc with
  | Elocal n -> name ff n
  | Eglobal { lname } -> longname ff lname
  | Eop(op, e_list) -> operator ff op e_list
  | Elast x -> fprintf ff "last %a" name x
  | Econstr0(ln) -> longname ff ln
  | Econst c -> immediate ff c
  | Eapp({ app_inline; app_statefull }, e, e_list) ->
     fprintf ff "@[(%s%s%a %a)@]"
       (if app_inline then "inline " else "")
       (if app_statefull then "run " else "")
       expression e (print_list_r expression "" "" "") e_list
  | Econstr1(ln, e_list) ->
     fprintf ff "@[%a%a@]"
       longname ln (print_list_r expression "("","")") e_list
  | Etuple(e_list) ->
     fprintf ff "@[%a@]" (print_list_r expression "("","")") e_list
  | Erecord_access(e, field) ->
     fprintf ff "@[%a.%a@]" expression e longname field
  | Erecord(ln_e_list) ->
     print_record (print_couple longname expression """ =""") ff ln_e_list
  | Erecord_with(e, ln_e_list) ->
     fprintf ff "@[{ %a with %a }@]"
       expression e
       (print_list_r
	  (print_couple longname expression """ =""") "" ";" "")
       ln_e_list
  | Elet(l, e) ->
     fprintf ff "@[<v 0>%a@ %a@]" local l expression e
  | Eblock(b, e) ->
     fprintf ff "@[<v 0>%a in@ %a@]"
       block_of_equation b expression e
  | Etypeconstraint(e, typ) ->
     fprintf ff "@[(%a: %a)@]" expression e ptype typ
  | Eseq(e1, e2) ->
     fprintf ff "@[%a;@,%a@]" expression e1 expression e2
  | Eperiod(p) ->
     fprintf ff "@[period %a@]" (period expression) p
  | Ematch(total, e, m_h_list) ->
     fprintf ff "@[<v>@[<hov 2>%smatch %a with@ @[%a@]@]@]"
       (if !total then "total " else "")
       expression e (print_list_l (match_handler expression) """""")
       m_h_list
  | Epresent(p_h_list, opt_e) ->
     fprintf ff "@[<v>@[<hov 2>present@ @[%a@]@]@ @[%a@]@]"
       (print_list_l (present_handler (scondpat expression) expression)
	  """""") p_h_list
       (print_opt2 expression "else ") opt_e
  | Ereset(e_body, e) ->
     fprintf ff "@[<hov>reset@ %a@ every %a@]" expression e_body expression e
  | Eautomaton(is_weak, s_h_list, e_opt) ->
     automaton_handler_list
       is_weak block_of_expression block_of_expression expression
       ff s_h_list e_opt

and operator ff op e_list =
  match op, e_list with
  | Eunarypre, [e] -> fprintf ff "pre %a" expression e
  | Efby, [e1;e2] ->
     fprintf ff "%a fby %a" expression e1 expression e2
  | Eminusgreater, [e1;e2] ->
     fprintf ff "%a -> %a" expression e1 expression e2
  | Eifthenelse,[e1;e2;e3] ->
     fprintf ff "@[(if %a then %a@ else %a)@]"
       expression e1 expression e2 expression e3
  | Eup, [e] ->
     fprintf ff "up %a" expression e
  | Etest, [e] ->
     fprintf ff "? %a" expression e
  | Edisc, [e] ->
     fprintf ff "disc %a" expression e
  | Ehorizon, [e] ->
     fprintf ff "@[horizon@ @[%a@]@]" expression e
  | Einitial, [] ->
     fprintf ff "init"
  | Eaccess, [e1; e2] ->
     fprintf ff "@[%a.(%a)@]" expression e1 expression e2
  | Eupdate, [e1; i; e2] ->
     fprintf ff "@[{%a with@ (%a) = %a}@]"
       expression e1 expression i expression e2
  | Eatomic, [e] ->
     fprintf ff "atomic %a" expression e
  | _ -> assert false

and equation ff ({ eq_desc = desc } as eq) =
  print_eq_info ff eq;
  match desc with
  | EQeq(p, e) ->
     fprintf ff "@[<hov 2>%a =@ %a@]" pattern p expression e
  | EQder(n, e, e0_opt, []) ->
     fprintf ff "@[<hov 2>der %a =@ %a %a@]"
       name n expression e
       (optional_unit
          (fun ff e -> fprintf ff "init %a " expression e)) e0_opt
  | EQder(n, e, e0_opt, p_h_list) ->
     fprintf ff "@[<hov 2>der %a =@ %a %a@ @[<hov 2>reset@ @[%a@]@]@]"
       name n expression e
       (optional_unit
          (fun ff e -> fprintf ff "init %a " expression e)) e0_opt
       (print_list_l (present_handler (scondpat expression)
                        expression) "" "" "")
       p_h_list
  | EQinit(n, e0) ->
     fprintf ff "@[<hov2>init %a =@ %a@]" name n expression e0
  | EQpluseq(n, e) ->
     fprintf ff "@[<hov2>%a +=@ %a@]" name n expression e
  | EQnext(n, e, None) ->
     fprintf ff "@[<hov 2>next %a =@ %a@]"
       name n expression e
  | EQnext(n, e, Some(e0)) ->
     fprintf ff "@[<hov2>next %a =@ @[%a@ init %a@]@]"
       name n expression e expression e0
  | EQautomaton(is_weak, s_h_list, e_opt) ->
     automaton_handler_list
       is_weak block_of_equation block_of_equation expression
       ff s_h_list e_opt
  | EQmatch(total, e, m_h_list) ->
     fprintf ff "@[<hov0>%smatch %a with@ @[%a@]@]"
       (if !total then "total " else "")
       expression e
       (print_list_l
	  (match_handler equation) """""")
       m_h_list
  | EQifthenelse(e, eq1, eq2) ->
     fprintf ff "@[<hov0>if %a@ then %a@ else %a@]"
       expression e equation eq1 equation eq2
  | EQpresent(p_h_list, None) ->
     fprintf ff "@[<hov0>present@ @[%a@]@]"
       (print_list_l
	  (present_handler (scondpat expression) equation) """""") p_h_list
  | EQpresent(p_h_list, Some(eq)) ->
     fprintf ff "@[<hov0>present@ @[%a@]@ else @[%a@]@]"
       (print_list_l
	  (present_handler (scondpat expression) equation) """""") p_h_list
       equation eq
  | EQreset(eq, e) ->
     fprintf ff "@[<hov2>reset@ @[%a@]@ @[<hov 2>every@ %a@]@]"
       equation eq expression e
  | EQemit(n, opt_e) ->
     begin match opt_e with
     | None -> fprintf ff "@[emit %a@]" name n
     | Some(e) ->
        fprintf ff "@[emit %a = %a@]" name n expression e
     end
  | EQblock(b_eq) -> block_of_equation ff b_eq
  | EQand(and_eq_list) ->
     print_list_l equation "do " "and " " done" ff and_eq_list
  | EQbefore(b_eq_list) ->
     print_list_l equation "" "before " "" ff b_eq_list
  | EQforall { for_index = i_list; for_init = init_list; for_body = b_eq;
	       for_in_env = in_env; for_out_env = out_env } ->
     let index ff { desc = desc } =
       match desc with
       | Einput(i, e) ->
	  fprintf ff "@[%a in %a@]" name i expression e
       | Eoutput(i, j) ->
	  fprintf ff "@[%a out %a@]" name i name j
       | Eindex(i, e1, e2) ->
	  fprintf ff
	    "@[%a in %a .. %a@]" name i expression e1 expression e2 in
     let init ff { desc = desc } =
       match desc with
       | Einit_last(i, e) ->
	  fprintf ff "@[last %a = %a@]" name i expression e in
     fprintf ff
       "@[<hov 2>forall %a@,@[<v>%a@,%a@,%a@ \
        @[<v 1>initialize@ @[<v>%a@]@]@ done @]@]"
       (print_list_r index "" "," "") i_list
       print_env in_env
       print_env out_env block_of_equation b_eq
       (print_list_l init "" "and " "") init_list
  | EQempty -> fprintf ff "()"
  | EQassert(e) ->
     fprintf ff "@[<hov2>assert %a@]" expression e
    
and block_of_equation ff b_eq =
  block locals expression equation ff b_eq

and block_of_expression ff b_exp =
  block locals expression expression ff b_exp

and equation_list po pf ff eq_list =
  match eq_list with
  | [] -> fprintf ff "%s%s" po pf
  | [eq] -> equation ff eq
  | _ -> print_list_l equation po "and " pf ff eq_list


and locals ff l =
  if l <> [] then fprintf ff "@[%a@]" (print_list_l local """""") l

and local ff { l_rec = is_rec; l_eq = eq_list; l_env = env } =
  let s = if is_rec then "rec " else "" in
  fprintf ff "@[<v 0>%alet %a@]"
    print_env env (equation_list s " in") eq_list

let constr_decl ff { desc = desc } =
  match desc with
  | Econstr0decl(n) -> fprintf ff "%s" n
  | Econstr1decl(n, ty_list) ->
      fprintf ff "@[%s of %a@]" n (print_list_l ptype "(" "* " ")") ty_list

let type_decl ff { desc = desc } =
  match desc with
    | Eabstract_type -> ()
    | Eabbrev(ty) ->
        fprintf ff " = %a" ptype ty
    | Evariant_type(constr_decl_list) ->
        fprintf
          ff " = %a" (print_list_l constr_decl "" "|" "") constr_decl_list
    | Erecord_type(n_ty_list) ->
        fprintf ff " = %a"
          (print_record (print_couple shortname ptype """ :""")) n_ty_list

(* Debug printer for (Ident.t * Deftypes.typ) Misc.State.t *)
let state_ident_typ =
  let fprint_v ff (id, ty) =
    fprintf ff "@[%a:%a@]" Ident.fprint_t id Ptypes.output ty in
  Misc.State.fprint_t fprint_v

(* Debug printer for Hybrid.eq Misc.State.t *)
let state_eq = Misc.State.fprint_t equation

let open_module ff n =
  fprintf ff "@[open ";
  shortname ff n;
  fprintf ff "@.@]"

let kind_of = function
  | V -> Tvalue
  | S -> Tstatic
  | A -> Tany
  | AD -> Tdiscrete(false)
  | C -> Tcont
  | D -> Tdiscrete(true)
  | P -> Tproba

(* print the kind [k] in a global constant decl. [let x = e] *)
(* or signature [val f : ty] *)
let fkind_of_const k =
  match k with
  | Tvalue -> "const "
  | Tstatic -> ""
  | Tany | Tdiscrete _ | _ -> assert false

let result ff { r_desc } =
  match r_desc with
  | Exp(e) -> expression ff e
  | Returns(b) ->
     block_of_equation ff b
    
let funexp ff { f_kind = k; f_args = p_list; f_body = b; f_env = env } =
  fprintf ff "@[<v 2>%s %a . @ %a%a@]"
    (match k with
     | V -> "vfun" | S -> "sfun" | A -> "fun" | AD -> "dfun"
     | D -> "node" | C -> "hybrid" | P -> "proba")
    (pattern_list "" "" "") p_list print_env env result b

let implementation ff impl =
  match impl.desc with
    | Eopen(n) -> open_module ff n
    | Etypedecl(n, params, ty_decl) ->
        fprintf ff "@[<v 2>type %a%s %a@.@.@]"
          Ptypes.print_type_params params
          n type_decl ty_decl
    | Econstdecl(n, k, e) ->
        fprintf ff "@[<v 2>let %s%a =@ %a@.@.@]"
          (fkind_of_const (kind_of k)) shortname n expression e
    | Efundecl(n, body) ->
       fprintf ff "@[<v 2>let %a =@ %a@.@]" shortname n funexp body

let program ff imp_list =
  List.iter (implementation ff) imp_list

let interface ff inter =
  match inter.desc with
    | Einter_open(n) -> open_module ff n
    | Einter_typedecl(n, params, ty_decl) ->
        fprintf ff "@[<v 2>type %a%s %a@.@.@]"
          Ptypes.print_type_params params
          n type_decl ty_decl
    | Einter_constdecl(n, k, ty) ->
        fprintf ff "@[<v 2>val %s%a : %a@.@.@]"
          (fkind_of_const (kind_of k)) shortname n ptype ty

let interface_list ff int_list =
  List.iter (interface ff) int_list
   *)
