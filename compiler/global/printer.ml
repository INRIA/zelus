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
(* the printer *)

open Location
open Misc
open Zelus
open Deftypes
open Ptypes
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

let longname ff ln =
  let ln = Initial.short (currentname ln) in
  match ln with
    | Lident.Name(m) -> shortname ff m
    | Lident.Modname({ Lident.qual = m; Lident.id = s }) -> 
        fprintf ff "%s.%s" m (parenthesis s)

let name ff n = shortname ff (Ident.name n)
          
let immediate ff = function 
  | Eint i -> fprintf ff "%d" i
  | Efloat f -> fprintf ff "%f" f
  | Ebool b -> if b then fprintf ff "true" else fprintf ff "false"
  | Estring s -> fprintf ff "%S" s
  | Echar c -> fprintf ff "'%c'" c
  | Evoid -> fprintf ff "()"
   
let constant ff = function
  | Cimmediate(i) -> immediate ff i
  | Cglobal(ln) -> longname ff ln 

let rec pattern ff ({ p_caus = caus_list } as pat) =
  let rec pattern ff pat =
    match pat.p_desc with
    | Evarpat(n) -> name ff n
    | Ewildpat -> fprintf ff "_"
    | Econstpat(im) -> immediate ff im
    | Econstr0pat(ln) -> longname ff ln
    | Etuplepat(pat_list) -> pattern_list ff pat_list
    | Etypeconstraintpat(p, ty_exp) ->
        fprintf ff "(%a:%a)" pattern p ptype ty_exp
    | Erecordpat(n_pat_list) ->
        print_record (print_couple longname pattern """ =""") ff n_pat_list
    | Ealiaspat(p, n) ->
        fprintf ff "%a as %a" pattern p name n
    | Eorpat(pat1, pat2) ->
       fprintf ff "%a | %a" pattern pat1 pattern pat2 in
(* fprintf ff "@[%a (* caus: %a *)@]" pattern pat Pcaus.caus_list caus_list *)
  pattern ff pat
  

and pattern_list ff pat_list =
  fprintf ff "@[%a@]" (print_list_r pattern "("","")") pat_list

and ptype ff ty =
  match ty.desc with
    | Etypevar(s) -> fprintf ff "%s" s
    | Etypeconstr(ln, ty_list) -> 
        fprintf ff "@[<hov2>%a@]%a" 
          (print_list_r_empty ptype "("","")") ty_list 
          longname ln
    | Etypetuple(ty_list) ->
        fprintf ff "@[<hov2>%a@]" (print_list_r ptype "(""*"")") ty_list
        
let print_vardec_list ff vardec_list =  
  let default ff = function
    | Init(v) -> fprintf ff " init %a" constant v
    | Default(v) -> fprintf ff " default %a" constant v in
  let combine ff v = fprintf ff " with %a" longname v in
  let vardec ff
      { vardec_name = n; vardec_default = d_opt; vardec_combine = c_opt } =
    fprintf ff "@[%a%a%a@]" name n
      (Misc.optional_unit default) d_opt (Misc.optional_unit combine) c_opt in
  if vardec_list <> [] 
  then fprintf ff "@[<v 2>%a@ @]"
    (print_list_r vardec "local " "," " in") vardec_list

let print_binding ff (n, { t_sort = sort; t_typ = typ }) =
  let default ff v = fprintf ff " default %a" constant v in
  let combine ff v = fprintf ff " with %a" longname v in
  let init ff i_opt =
    match i_opt with
    | None -> fprintf ff " initialized"
    | Some(c) -> fprintf ff " init %a" constant c in
  let next ff is_n = if is_n then fprintf ff "next " in
  let previous p = if p then "last " else "" in
  let kind ff k =
    let k = match k with
      | Cont -> "cont" | Zero -> "zero"
      | Period -> "period" | Horizon -> "horizon" | Encore -> "encore" in
    fprintf ff " %s " k in
  match sort with
  | Sval -> fprintf ff "@[val %a: %a@,@]" name n Ptypes.output typ
  | Svar { v_combine = c_opt; v_default = d_opt } ->
     fprintf ff "@[var %a: %a%a%a@,@]" name n Ptypes.output typ
	     (Misc.optional_unit default) d_opt
	     (Misc.optional_unit combine) c_opt
  | Smem { m_kind = k; m_next = n_opt; m_previous = p;
	   m_init = i_opt; m_combine = c_opt } ->
     fprintf ff "@[%a%s%amem %a: %a%a%a@,@]"
	     (Misc.optional_unit next) n_opt (previous p) 
	     (Misc.optional_unit kind) k name n Ptypes.output typ
	     (Misc.optional_unit init) i_opt
	     (Misc.optional_unit combine) c_opt

let print_env ff env =
  let env = Ident.Env.bindings env in
  if env <> [] then
    fprintf ff "@[<v 0>(* defs: %a *)@ @]" 
      (print_list_r print_binding """;""") env

let print_writes ff { dv = dv; di = di; der = der } =
  let dv = Ident.S.elements dv in
  let di = Ident.S.elements di in
  let der = Ident.S.elements der in
  open_box 0;
  if dv <> [] then 
    fprintf ff "@[<v 0>(* dv = {@[%a@]} *)@ @]" (print_list_r name "" "," "") dv;
  if di <> [] then
    fprintf ff "@[<v 0>(* di = {@[%a@]} *)@ @]" (print_list_r name "" "," "") di;
  if der <> [] then
    fprintf ff "@[<v 0>(* der = {@[%a@]} *)@ @]" (print_list_r name "" "," "") der;
  close_box ()
      
(* print a block surrounded by two braces [po] and [pf] *)
let block locals body po pf ff 
    { b_vars = vardec_list; b_locals = l; b_body = b; b_write = w; b_env = n_env } =
  fprintf ff "@[<hov 0>%a%a%a%a%a@]"
    print_vardec_list vardec_list
    print_writes w
    print_env n_env
    locals l
    (body po pf) b

let match_handler body ff { m_pat = pat; m_body = b; m_env = env;
			    m_reset = r; m_zero = z } =
  fprintf ff "@[<hov 4>| %a -> %s%s@ %a%a@]" 
    pattern pat (if r then "(* reset *)" else "")
                (if z then "(* zero *)" else "")
		print_env env body b

let present_handler scondpat body ff { p_cond = scpat; p_body = b; p_env = env } =
  fprintf ff "@[<hov 2>| (%a) ->@ @[<v 0>%a%a@]@]" 
    scondpat scpat print_env env body b

let rec expression ff e =
  match e.e_desc with
    | Elocal n -> name ff n
    | Eglobal ln -> longname ff ln
    | Elast x -> fprintf ff "last %a" name x
    | Econstr0(ln) -> longname ff ln
    | Econst c -> immediate ff c
    | Eapp(op, e_list) -> operator op ff e_list
    | Etuple(e_list) ->
        fprintf ff "@[%a@]" (print_list_r expression "("","")") e_list
    | Erecord_access(e, field) ->
        fprintf ff "@[%a.%a@]" expression e longname field
    | Erecord(ln_e_list) ->
        print_record (print_couple longname expression """ =""") ff ln_e_list
    | Elet(l, e) ->
        fprintf ff "@[<v 0>%a@ %a@]" local l expression e
    | Eblock(b, e) ->
       fprintf ff "@[<v 0>%a@ %a@]" (block_equation_list "do " "in") b expression e
    | Etypeconstraint(e, typ) ->
        fprintf ff "@[(%a: %a)@]" expression e ptype typ
    | Eseq(e1, e2) ->
        fprintf ff "@[%a;@,%a@]" expression e1 expression e2
    | Eperiod(p) ->
        fprintf ff "@[period %a@]" period p    
    | Ematch(total, e, match_handler_list) ->
        fprintf ff "@[<v>@[<hov 2>%smatch %a with@ @[%a@]@]@]"
          (if !total then "total " else "")
          expression e (print_list_l (match_handler expression) """""") 
	  match_handler_list
    | Epresent(present_handler_list, opt_e) ->
        fprintf ff "@[<v>@[<hov 2>present@ @[%a@]@]@ @[%a@]@]"
          (print_list_l (present_handler scondpat expression)
	     """""") present_handler_list
          (print_opt2 expression "else ") opt_e

and operator op ff e_list =
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
    | Eafter(n_list), [e] ->
       fprintf ff "@[%a@ after@ @[%a@]@]" expression e
	       (print_list_r name "("","")") n_list
    | Ehorizon, [e] ->
       fprintf ff "@[horizon@ @[%a@]@]" expression e
    | Einitial, _ -> 
        fprintf ff "init"
    | Eop(is_inline, f), e_list -> 
        fprintf ff "@[%s%a%a@]" (if is_inline then "inline " else "")
          longname f (print_list_r expression "("","")") e_list
    | Eevery(is_inline, f), e :: e_list -> 
        fprintf ff "@[%s%a%a every %a@]" (if is_inline then "inline " else "")
          longname f (print_list_r expression "("","")") e_list expression e
    | Eafter _, e_list ->
       print_newline ();
       print_int (List.length e_list);
       print_newline ();
       flush stdout;
       raise Not_found
    | (Eevery _ | Ehorizon | Edisc | Etest | Eup | Eifthenelse
       | Eminusgreater | Efby | Eunarypre), _ -> assert false
						       
and period ff { p_phase = opt_phase; p_period = p } =
  match opt_phase with
    | None -> fprintf ff "@[(%f)@]" p
    | Some(phase) -> fprintf ff "@[%f(%f)@]" phase p
        
and equation ff { eq_desc = desc; eq_write = w } =
  print_writes ff w;
  match desc with
    | EQeq(p, e) ->
      fprintf ff "@[<hov 2>%a =@ %a@]" pattern p expression e
    | EQder(n, e, e0_opt, []) ->
      fprintf ff "@[<hov 2>der %a =@ %a %a@]"
        name n expression e 
        (optional_unit 
           (fun ff e -> fprintf ff "init %a " expression e)) e0_opt
    | EQder(n, e, e0_opt, present_handler_list) ->
      fprintf ff "@[<hov 2>der %a =@ %a %a@ @[<hov 2>reset@ @[%a@]@]@]"
        name n expression e 
        (optional_unit 
           (fun ff e -> fprintf ff "init %a " expression e)) e0_opt
        (print_list_l (present_handler scondpat expression) """""") 
	present_handler_list
    | EQinit(n, e0) ->
      fprintf ff "@[<hov 2>init %a =@ %a@]" name n expression e0
    | EQpluseq(n, e) ->
      fprintf ff "@[<hov 2>%a +=@ %a@]" name n expression e
    | EQnext(n, e, None) ->
      fprintf ff "@[<hov 2>next %a =@ %a@]" 
	name n expression e
    | EQnext(n, e, Some(e0)) ->
      fprintf ff "@[<hov 2>next %a =@ @[%a@ init %a@]@]"
	name n expression e expression e0
    | EQautomaton(is_weak, s_h_list, e_opt) ->
      fprintf ff "@[<v>@[<hov 0>automaton%s@ @[%a@]@]%a@]"
	      (if is_weak then "(* weak *)" else "(* strong *)")
	      (state_handler_list is_weak) s_h_list
	      (print_opt (print_with_braces state " init" "")) e_opt
    | EQmatch(total, e, match_handler_list) ->
      fprintf ff "@[<v>@[<hov 0>%smatch %a with@ @[%a@]@]@]"
        (if !total then "total " else "")
        expression e 
	(print_list_l 
	   (match_handler (block_equation_list "do " "done")) """""") 
	match_handler_list
    | EQpresent(present_handler_list, None) ->
      fprintf ff "@[<v>@[<hov 0>present@ @[%a@]@]@]"
        (print_list_l 
	   (present_handler scondpat (block_equation_list "do " "done")) 
	   """""") present_handler_list
    | EQpresent(present_handler_list, Some(b)) ->
      fprintf ff "@[<v>@[<hov 0>present@ @[%a@]@]@ else @[%a@]@]"
        (print_list_l 
	   (present_handler scondpat (block_equation_list "do " "done")) 
	   """""")  present_handler_list
        (block_equation_list "do " "done")  b
    | EQreset(eq_list, e) ->
      fprintf ff "@[<v>@[<hov 2>reset@ @[%a@]@]@ @[<hov 2>every@ %a@]@]"
        (equation_list "" "") eq_list expression e
    | EQemit(n, opt_e) ->
      begin match opt_e with
        | None -> fprintf ff "@[emit %a@]" name n
        | Some(e) ->
          fprintf ff "@[emit %a = %a@]" name n expression e
      end
    | EQblock(b_eq_list) -> block_equation_list "do " "done" ff b_eq_list

and block_equation_list po pf ff b = block locals equation_list po pf ff b

and equation_list po pf ff eq_list = 
  print_list_l equation po "and " pf ff eq_list

and state_handler_list is_weak ff s_h_list = 
  print_list_l (state_handler is_weak) """""" ff s_h_list

and state_handler is_weak ff
    { s_state = s; s_body = b; s_trans = trans; s_env = env } =
  let print ff trans =
    if trans = [] then fprintf ff "done"
    else 
      print_list_r escape 
		   (if is_weak then "until " else "unless ") "" "" ff trans in
  fprintf ff "@[<v 4>| %a -> %a@[<v>%a@,%a@]@]" 
	 statepat s print_env env (block_equation_list "do " "") b print trans
   

and escape ff { e_cond = scpat; e_reset = r; e_block = b_opt; 
		e_next_state = ns; e_env = env } =
  match b_opt with
    | None ->
        fprintf ff "| %a %a%s %a"
          scondpat scpat print_env env (if r then "then" else "continue") state ns
    | Some(b) ->
        fprintf ff "| %a %a%s %a in %a"
          scondpat scpat print_env env (if r then "then" else "continue") 
          (block_equation_list "do " "") b state ns

and scondpat ff scpat = match scpat.desc with
  | Econdand(scpat1, scpat2) -> 
      fprintf ff "@[%a &@ %a@]" scondpat scpat1 scondpat scpat2
  | Econdor(scpat1, scpat2) -> 
      fprintf ff "@[%a |@ %a@]" scondpat scpat1 scondpat scpat2
  | Econdexp(e) -> expression ff e
  | Econdpat(e, pat) -> fprintf ff "%a(%a)" expression e pattern pat
  | Econdon(scpat1, e) -> 
      fprintf ff "@[%a on@ %a@]" scondpat scpat1 expression e
  

and statepat ff spat = match spat.desc with
  | Estate0pat(n) -> name ff n
  | Estate1pat(n, n_list) ->
      fprintf ff "%a%a" name n (print_list_r name "("","")") n_list

and state ff se = match se.desc with
  | Estate0(n) -> name ff n
  | Estate1(n, e_list) ->
      fprintf ff "%a%a" name n (print_list_r expression "("","")") e_list

and locals ff l = 
  if l <> [] then fprintf ff "@[%a@]" (print_list_l local """""") l

and local ff { l_eq = eq_list; l_env = env } = 
  fprintf ff "@[<v 0>%alet %a@]"
	  print_env env (equation_list "rec " "in") eq_list
 
         
let type_decl ff ty_decl =
  match ty_decl with
    | Eabstract_type -> ()
    | Eabbrev(ty) ->
        fprintf ff " = %a" ptype ty
    | Evariant_type(tag_name_list) ->
        fprintf ff " = %a" (print_list_l shortname "" "|" "") tag_name_list
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
    
let implementation ff impl =
  match impl.desc with
    | Eopen(n) -> open_module ff n
    | Etypedecl(n, params, ty_decl) ->
        fprintf ff "@[<v 2>type %a%s %a@.@.@]"
          print_type_params params
          n type_decl ty_decl
    | Econstdecl(n, e) ->
        fprintf ff "@[<v 2>let %s =@ %a@.@.@]"
          n expression e 
    | Efundecl(n, { f_kind = k; f_args = p_list; f_body = e; f_env = env }) ->
        fprintf ff "@[<v 2>let %s %s%a =@ %a%a@.@.@]"
          (match k with | A -> "pure" | AD -> "" | D -> "node" | C -> "hybrid")
          n pattern_list p_list print_env env expression e

let implementation_list ff imp_list =
  List.iter (implementation ff) imp_list

let interface ff inter =
  match inter.desc with
    | Einter_open(n) -> open_module ff n
    | Einter_typedecl(n, params, ty_decl) ->
        fprintf ff "@[<v 2>type %a%s %a@.@.@]"
          print_type_params params
          n type_decl ty_decl
    | Einter_constdecl(n, ty) ->
        fprintf ff "@[<v 2>val %s : %a@.@.@]"
          n ptype ty
    | Einter_fundecl(n, signature) ->
        fprintf ff "@[<v 2>val %s %s : %a %s %a@.@.@]"
          (if signature.sig_safe then "safe" else "") n
          (print_list_r ptype "("" *"")") signature.sig_inputs
          (match signature.sig_kind 
	   with | A -> "-A->" | AD -> "-AD->" | D -> "-D->" | C -> "-C->")
          ptype signature.sig_output

let interface_list ff int_list =
  List.iter (interface ff) int_list

