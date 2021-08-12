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
     let s =
       match k with | Kfun -> "->" | Khybrid | Knode -> "=>" | Kstatic -> ">" in
     fprintf ff "@[<hov2>%a %s %a@]" ptype ty_arg s ptype ty_res

     
let print_record print1 print2 po sep pf ff { label; arg } =
  fprintf ff "@[<hov>%s@[%a@]%s@ @[%a@]%s@]" po print1 label sep print2 arg pf


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
     print_list_r
       (print_record longname pattern "" " =" "") "{" ";" "}" ff n_pat_list
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
  
let vardec_list exp ff vardec_list =
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
    (vardec_list exp) b_vars
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

let default body ff default_opt =
  match default_opt with
  | Init(b) -> fprintf ff "@[<hov2>init@,%a@]" body b
  | Else(b) -> fprintf ff "@[<hov2>else@,%a@]" body b
  | NoDefault -> ()

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

let automaton_handler_list
      is_weak leqs body body_in_escape expression ff s_h_list e_opt =
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

  (* test whether a block is empty or not *)
  let is_empty_block { b_body = { eq_desc } } = eq_desc = EQempty in
  
  let automaton_handler is_weak body body_in_escape expression ff
        { s_state; s_let; s_body; s_trans; s_env } =
    
    let escape ff { e_cond; e_let; e_reset; e_body;
		    e_next_state; e_env } =
      leqs ff e_let;
      if is_empty_block e_body
      then
        fprintf ff "@[<v4>| %a %a%s@ %a@]"
          (scondpat expression) e_cond print_env e_env
          (if e_reset then "then" else "continue") state e_next_state
      else
         fprintf ff "@[<v4>| %a %a%s@ %a in %a@]"
           (scondpat expression) e_cond print_env e_env
           (if e_reset then "then" else "continue")
           body_in_escape e_body state e_next_state in
    
    let escape_list ff t_list =
      if t_list = [] then fprintf ff "done"
      else
        print_list_r escape
	  (if is_weak then "until " else "unless ") "" "" ff t_list in
    fprintf ff "@[<v 4>| %a ->@ %a@[<v0>%a%a@,%a@]@]"
      statepat s_state print_env s_env
      leqs s_let body s_body escape_list s_trans in
  
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
  let exp ff e =
    match e.e_desc with
    | Elocal n -> name ff n
    | Eglobal { lname } -> longname ff lname
    | Eop(op, e_list) -> operator ff op e_list
    | Elast x -> fprintf ff "last %a" name x
    | Econstr0 { lname } -> longname ff lname
    | Econst c -> immediate ff c
    | Eapp(e, e_list) ->
       fprintf ff "@[(%a %a)@]"
         expression e (print_list_r expression "" "" "") e_list
    | Econstr1 { lname; arg_list } ->
       fprintf ff "@[%a%a@]"
         longname lname (print_list_r expression "(" "," ")") arg_list
    | Etuple(e_list) ->
       fprintf ff "@[%a@]" (print_list_r expression "(" "," ")") e_list
    | Erecord_access { label; arg } ->
       fprintf ff "@[%a.%a@]" expression arg longname label
    | Erecord(ln_e_list) ->
       print_list_r
         (print_record longname expression "" " =" "") "{" ";" "}" ff ln_e_list
    | Erecord_with(e, ln_e_list) ->
       fprintf ff "@[{ %a with %a }@]"
         expression e
         (print_list_r
	    (print_record longname expression """ =""") "" ";" "")
         ln_e_list
    | Elet(l, e) ->
       fprintf ff "@[<v 0>%a@ %a@]" leq l expression e
    | Etypeconstraint(e, typ) ->
       fprintf ff "@[(%a: %a)@]" expression e ptype typ
    | Ematch { is_total; e; handlers } ->
       fprintf ff "@[<v>@[<hov 2>%smatch %a with@ @[%a@]@]@]"
         (if is_total then "total " else "")
         expression e (print_list_l (match_handler expression) """""")
         handlers
    | Epresent { handlers; default_opt } ->
       fprintf ff "@[<v>@[<hov 2>present@ @[%a@]@]@ @[%a@]@]"
         (print_list_l (present_handler (scondpat expression) expression)
	    """""") handlers
         (default expression) default_opt
    | Ereset(e_body, e) ->
       fprintf ff "@[<hov>reset@ %a@ every %a@]" expression e_body expression e
    | Efun(fe) ->
       funexp ff fe in
  if Deftypes.is_no_typ e.e_typ && !vverbose then
    fprintf ff "@[<hov 2>(%a :@ %a)@]" exp e Ptypes.output e.e_typ
  else exp ff e
  
and result ff { r_desc } =
  match r_desc with
  | Exp(e) -> expression ff e
  | Returns(b) -> return_block ff b
                
and return_block ff { b_vars; b_body; b_write; b_env } =
  fprintf ff "@[<hov 0>returns @[(%a)@]@ @[%a@]@ @[%a@]@ @[%a@]@]"
    (vardec_list expression) b_vars
    print_writes b_write
    print_env b_env
    equation b_body
  
and funexp ff { f_kind; f_args; f_body; f_env } =
  let s =
    match f_kind with
    | Kstatic -> ">" | Kfun -> "->" | Khybrid | Knode -> "=>" in
  fprintf ff "@[<v 2>fun %a %s @ %a%a@]"
    arg_list f_args s print_env f_env result f_body

and arg_list ff a_list =
  print_list_r (vardec_list expression) "(" "" ")" ff a_list
  
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
  | Eatomic, [e] ->
     fprintf ff "atomic %a" expression e
  | Eperiod, [e1; e2] ->
     fprintf ff "period %a(%a)" expression e1 expression e2
  | Eseq, [e1; e2] ->
     fprintf ff "@[%a;@,%a@]" expression e1 expression e2
  | Erun(is_inline), [e1; e2] ->
     fprintf ff "@[%srun@ %a@ %a@]"
       (if is_inline then "inline " else "") expression e1 expression e2
  | _ -> assert false

and equation ff ({ eq_desc = desc } as eq) =
  print_eq_info ff eq;
  match desc with
  | EQeq(p, e) ->
     fprintf ff "@[<hov 2>%a =@ %a@]" pattern p expression e
  | EQder(n, e, e0_opt, []) ->
      fprintf ff "@[<hov 2>der %a =@ %a%a@]"
        name n expression e
        (Util.optional_unit
           (fun ff e -> fprintf ff " init %a " expression e)) e0_opt
  | EQder(n, e, e0_opt, handlers) ->
     fprintf ff "@[<hov 2>der %a =@ %a %a@ @[<hov 2>reset@ @[%a@]@]@]"
       name n expression e
       (Util.optional_unit
          (fun ff e -> fprintf ff "init %a " expression e)) e0_opt
       (print_list_l (present_handler (scondpat expression) expression) """""")
       handlers
  | EQinit(n, e) ->
     fprintf ff "@[<hov2>init %a =@ %a@]" name n expression e
  | EQemit(n, opt_e) ->
     begin match opt_e with
     | None -> fprintf ff "@[emit %a@]" name n
     | Some(e) ->
        fprintf ff "@[emit %a = %a@]" name n expression e
     end
  | EQautomaton { is_weak; handlers; state_opt } ->
     automaton_handler_list
       is_weak leqs block_of_equation block_of_equation expression
       ff handlers state_opt
  | EQmatch { is_total; e; handlers } ->
     fprintf ff "@[<hov0>%smatch %a with@ @[%a@]@]"
       (if is_total then "total " else "")
       expression e
       (print_list_l (match_handler equation) """""") handlers
  | EQif(e, eq1, eq2) ->
     fprintf ff "@[<hov0>if %a@ then %a@ else %a@]"
       expression e equation eq1 equation eq2
  | EQpresent { handlers; default_opt } ->
     fprintf ff "@[<hov0>present@ @[%a@]@%a]"
       (print_list_l
	  (present_handler (scondpat expression) equation) """""") handlers
       (default equation) default_opt
  | EQreset(eq, e) ->
     fprintf ff "@[<hov2>reset@ @[%a@]@ @[<hov 2>every@ %a@]@]"
       equation eq expression e
  | EQlet(l_eq, eq) ->
     fprintf ff "@[<hov0>%a@ in@ %a@]" leq l_eq equation eq
  | EQlocal(b_eq) -> block_of_equation ff b_eq
  | EQand(and_eq_list) ->
     print_list_l equation "do " "and " " done" ff and_eq_list
  | EQempty -> fprintf ff "()"
  | EQassert(e) ->
     fprintf ff "@[<hov2>assert %a@]" expression e
    
and block_of_equation ff b_eq =
  block expression equation ff b_eq

and block_of_expression ff b_exp =
  block expression expression ff b_exp

and equation_list po pf ff eq_list =
  match eq_list with
  | [] -> fprintf ff "%s%s" po pf
  | [eq] -> equation ff eq
  | _ -> print_list_l equation po "and " pf ff eq_list

and leq ff { l_rec; l_eq; l_env } =
  let s = if l_rec then "rec " else "" in
  fprintf ff "@[<v0>%alet %s%a@ in@,@]"
    print_env l_env s equation l_eq

and leqs ff l =
  if l <> [] then fprintf ff "@[%a@]" (print_list_l leq "" "" "") l

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
          (print_list_r
             (print_couple shortname ptype "" " :" "") "{" ";" "}") n_ty_list

(* Debug printer for (Ident.t * Deftypes.typ) Misc.State.t *)
let state_ident_typ =
  let fprint_v ff (id, ty) =
    fprintf ff "@[%a:%a@]" Ident.fprint_t id Ptypes.output ty in
  State.fprint_t fprint_v

(* Debug printer for Hybrid.eq Misc.State.t *)
let state_eq = State.fprint_t equation

let open_module ff n =
  fprintf ff "@[open ";
  shortname ff n;
  fprintf ff "@.@]"

let implementation ff impl =
  match impl.desc with
    | Eopen(n) -> open_module ff n
    | Etypedecl(n, params, ty_decl) ->
        fprintf ff "@[<v 2>type %a%s %a@.@.@]"
          Ptypes.print_type_params params
          n type_decl ty_decl
    | Eletdecl(n, e) ->
        fprintf ff "@[<v 2>let %a =@ %a@.@]" shortname n expression e

let program ff imp_list = List.iter (implementation ff) imp_list

let interface ff { desc } =
  match desc with
  | Einter_open(n) -> open_module ff n
  | Einter_typedecl(n, params, ty_decl) ->
     fprintf ff "@[<v 2>type %a%s %a@.@.@]"
       Ptypes.print_type_params params
       n type_decl ty_decl
  | Einter_constdecl(n, ty, n_list) ->
     let print_n ff n = fprintf ff "%s" n in
     fprintf ff "@[<v 2>val %s : %a%a@.@]"
       n ptype ty (print_list_r print_n "=[" " " "]") n_list

let interface_list ff int_list =
  List.iter (interface ff) int_list
