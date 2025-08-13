(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2025 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* the printer *)
module type INFO =
  sig
    type info
    type ienv
    val no_info : info
    val print: Format.formatter -> info -> unit
    val pienv: Format.formatter -> ienv -> unit
  end

module Make (Info: INFO) =
  struct
    open Location
    open Misc
    open Zelus
    open Defnames
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
      match ln with
      | Lident.Name(m) -> shortname ff m
      | Lident.Modname(qual) -> qualident ff qual
    
    let type_longname ff ln =
      (* type names from the standard lib are printed without the prefix *)
      match ln with
      | Lident.Name(m) -> shortname ff m
      | Lident.Modname({ Lident.qual = m; Lident.id = s } as qual) ->
         if m = Misc.name_of_stdlib_module then shortname ff s
         else qualident ff qual

    let name ff n = shortname ff (Ident.name n)
    
    let source_name ff n = shortname ff (Ident.source n)
    
    let immediate ff = function
      | Eint i -> fprintf ff "%d" i
      | Efloat f -> fprintf ff "%f" f
      | Ebool b -> if b then fprintf ff "true" else fprintf ff "false"
      | Estring s -> fprintf ff "%S" s
      | Echar c -> fprintf ff "'%c'" c
      | Evoid -> fprintf ff "()"
    
    (* size expressions *)
    let size ff e =
      let operator =
        function Size_plus -> "+" | Size_minus -> "-" | Size_mult -> "*" in
      let priority_op =
        function Size_plus -> 0 | Size_minus -> 1 | Size_mult -> 3 in
      let priority s = match s with
        | Size_int _ | Size_var _ -> 3
        | Size_frac _ -> 2
        | Size_op(op, _, _) -> priority_op op in
      let rec size prio ff { desc } =
        let prio_s = priority desc  in
        if prio > prio_s then fprintf ff "(";
        begin match desc with
        | Size_int(i) -> fprintf ff "%d" i
        | Size_frac { num; denom } -> 
           fprintf ff "(%a/%d)" (size prio_s) num denom
        | Size_var(n) -> name ff n
        | Size_op(op, s1, s2) ->
           fprintf ff
             "@[%a %s %a@]" (size prio_s) s1 (operator op) (size prio_s) s2
        end;
        if prio > prio_s then fprintf ff ")" in
      size 0 ff e
    
    let rec ptype ff { desc } =
      match desc with
      | Etypevar(s) -> fprintf ff "'%s" s
      | Etypeconstr(ln, ty_list) ->
         fprintf ff "@[<hov2>%a@,%a@]"
           (print_list_r_empty ptype "("","")") ty_list type_longname ln
      | Etypetuple(ty_list) ->
         fprintf ff "@[<hov2>%a@]" (print_list_r ptype "(" " * " ")") ty_list
      | Etypefun { ty_kind; ty_name_opt; ty_arg; ty_res } ->
         let pas ff (n_opt, ty_arg) =
           match n_opt with
           | None -> ptype ff ty_arg 
           | Some(n) -> fprintf ff "(%a : %a)" name n ptype ty_arg in
         let s = match ty_kind with
           | Kfun(k) ->
              (match k with
               | Kconst -> "-V->" | Kstatic -> "-S->" | Kany -> "-A->" )
           | Knode(k) ->
              (match k with
               | Kdiscrete -> "-D->" | Kcont -> "-C->") in
         fprintf ff "@[<hov2>%a %s %a@]" pas (ty_name_opt, ty_arg) s ptype ty_res
      | Etypevec(ty, s) -> fprintf ff "@[[%a]]%a@]" size s ptype ty
    
    let print_type_params ff pl =
      print_list_r_empty (fun ff s -> fprintf ff "'%s" s) "("","") " ff pl
    
    let print_record print1 print2 po sep pf ff { label; arg } =
      fprintf ff
        "@[<hov>%s@[%a@]%s@ @[%a@]%s@]" po print1 label sep print2 arg pf
    
    let rec pattern ff { pat_desc; pat_info } =
      match pat_desc with
      | Evarpat(n) ->
         if !Misc.verbose then
           fprintf ff "@[(%a : %a)@]" name n Info.print pat_info
         else fprintf ff "%a" name n
      | Ewildpat -> fprintf ff "_"
      | Econstpat(im) -> immediate ff im
      | Econstr0pat(ln) -> longname ff ln
      | Econstr1pat(ln, pat_list) ->
         fprintf ff "@[%a%a@]" longname ln (pattern_list "(" "," ")") pat_list
      | Etuplepat(pat_list) ->
         pattern_list "(" "," ")" ff pat_list
      | Earraypat(pat_list) ->
         pattern_list "[|" ";" "|]" ff pat_list
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
    let out ff o_opt =
      match o_opt with | None -> () | Some(x) -> fprintf ff " out %a" name x
    
    let vardec exp ff
          { var_name = x; var_default = d_opt; var_init = i_opt; var_is_last; 
            var_init_in_eq } =
      fprintf ff "@[%s%a%a%a%s@]" 
        (if var_is_last then "last " else "")
        name x (init exp) i_opt (default exp) d_opt
        (if var_init_in_eq then " init ..." else "")
    
    let vardec_list exp ff vardec_list =
      print_if_not_empty
        (print_list_r (vardec exp) "" "," "") ff vardec_list
    
    let vkind ff k =
      match k with
      | Kconst -> fprintf ff " const"
      | Kstatic -> fprintf ff " static"
      | Kany -> fprintf ff ""
    
    let print_writes ff { dv ; di; der } =
      if !vverbose then begin
          let dv = Ident.S.elements dv in
          let di = Ident.S.elements di in
          let der = Ident.S.elements der in
          if dv <> [] then
            fprintf ff
  	      "@[<v 0>(* dv = {@[%a@]} *)@ @]" (print_list_r name "" "," "") dv;
          if di <> [] then
            fprintf ff
  	      "@[<v 0>(* di = {@[%a@]} *)@ @]" (print_list_r name "" "," "") di;
          if der <> [] then
            fprintf ff
  	      "@[<v 0>(* der = {@[%a@]} *)@ @]" (print_list_r name "" "," "") der
        end
    
    (* print an environment *)
    let print_env ff env =
      if !verbose && not (Ident.Env.is_empty env) then 
        fprintf ff "@[<v 0>(* %a *)@]"
          (Ident.Env.fprint_t Info.pienv) env
    
    (* print a hidden environment *)
    let print_hidden_env ff env =
      if not (Ident.Env.is_empty env) then 
        if !verbose then
          fprintf ff "@[<v 0>(* hidden env: %a *)@]"
          (Ident.Env.fprint_t Info.pienv) env
        else 
          Pp_tools.print_list_r
            (fun ff (x, _) -> Ident.fprint_t ff x) "(* {" "," "} *)" ff 
            (Ident.Env.to_list env)

    let print_eq_info ff { eq_write } =
      print_writes ff eq_write
    
    (* print a block *)
    let block exp body ff { b_vars; b_body; b_write; b_env } =
      match b_vars with
      | [] -> fprintf ff "@[<hov 0>%a@ %a@]" body b_body print_env b_env
      | _ ->
         fprintf ff "@[<hov 0>local@ %a@ %ado@ %a%a@]"
           (vardec_list exp) b_vars
           print_env b_env
           print_writes b_write       
           body b_body
    
    let match_handler body ff { m_pat; m_body; m_reset; m_zero; m_env } =
      fprintf ff "@[<hov 4>| %a@ %a -> %s%s@ %a@]"
        pattern m_pat
        print_env m_env
        (if m_reset then "(* reset *)" else "")
        (if m_zero then "(* zero *)" else "")
        body m_body
    
    let present_handler scondpat body ff { p_cond; p_body; p_env } =
      fprintf ff "@[<hov4>| (%a)@ %a ->@ @[<v 0>%a@]@]"
        scondpat p_cond  print_env p_env body p_body
    
    let with_default body ff default_opt =
      match default_opt with
      | Init(b) -> fprintf ff "@[<hov2>init@ %a@]" body b
      | Else(b) -> fprintf ff "@[<hov2>else@ %a@]" body b
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
    
    (* test whether a block is empty or not *)
    let is_empty_block { b_vars; b_body = { eq_desc } } =
      (b_vars = []) && (eq_desc = EQempty)
    
    let automaton_handler_list
          is_weak leqs body body_in_escape expression ff (s_h_list, e_opt) =
      let statepat ff { desc } = match desc with
        | Estate0pat(n) -> name ff n
        | Estate1pat(n, n_list) ->
           fprintf ff "%a%a" name n (print_list_r name "("","")") n_list in
      
      let rec state ff { desc } = match desc with
        | Estate0(n) -> name ff n
        | Estate1(n, e_list) ->
           fprintf ff "%a%a" name n (print_list_r expression "("","")") e_list
        | Estateif(e, se1, se2) ->
           fprintf ff "@[<hov0>if %a@ then %a@ else %a@]"
             expression e state se1 state se2 in
      
      let automaton_handler is_weak body body_in_escape expression ff
            { s_state; s_let; s_body; s_trans; s_env } =
        
        let escape ff { e_cond; e_let; e_reset; e_body;
		        e_next_state; e_env } =
          leqs ff e_let;
          if is_empty_block e_body
          then
            fprintf ff "@[<v4>| %a@ %a %s@ %a@]"
              (scondpat expression) e_cond
              print_env e_env
              (if e_reset then "then" else "continue") state e_next_state
          else
            fprintf ff "@[<v4>| %a@ %a %s@ %a in %a@]"
              (scondpat expression) e_cond
              print_env e_env
              (if e_reset then "then" else "continue")
              body_in_escape e_body 
              state e_next_state in
        
        let escape_list ff t_list =
          if t_list = [] then fprintf ff "done"
          else
            Pp_tools.print_list_r escape
	      (if is_weak then "until " else "unless ") "" "" ff t_list in
        fprintf ff "@[<v 4>| %a ->@ @[<v0>%a%a@,%a@]@]"
          statepat s_state
          leqs s_let body s_body escape_list s_trans in
      
      let automaton_handler_list ff s_h_list =
        print_list_l
          (automaton_handler is_weak body body_in_escape expression)
          """"""
          ff s_h_list in
      
      fprintf ff "@[<hov0>@[automaton%s@ %a@]@ %a@ end@]"
	(if is_weak then "(* weak *)" else "(* strong *)")
	automaton_handler_list s_h_list
	(Pp_tools.print_opt (Pp_tools.print_with_braces state "init " "")) e_opt
    
    let rec expression ff { e_desc; e_info } =
      match e_desc with
      | Evar n -> name ff n
      | Eglobal { lname } -> longname ff lname
      | Eop(op, e_list) -> 
         fprintf ff "@[(";
         operator ff op e_list;
         fprintf ff ")@]"
      | Elast { copy; id } ->
         fprintf ff "last%s %a" (if copy then "" else "*") name id
      | Econstr0 { lname } -> longname ff lname
      | Econst c -> immediate ff c
      | Eapp { is_inline; f; arg_list } ->
         fprintf ff "@[(";
         let s = if is_inline then "inline " else "" in
         fprintf ff "@[<hov2>%s%a@ %a@]"
           s expression f (print_list_r expression "" "" "") arg_list;
         fprintf ff ")@]"
      | Esizeapp { f; size_list } ->
         fprintf ff "@[(%a %a)@]" expression f
           (print_list_l size "<<" "," ">>") size_list 
      | Econstr1 { lname; arg_list } ->
         fprintf ff "@[(%a%a)@]"
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
         fprintf ff "@[<v0>(%a in@ %a)@]" leq l expression e
      | Elocal(b_eq, e) ->
         fprintf ff "@[<v0>(%a in @,%a)@]"
           block_of_equation b_eq expression e
      | Etypeconstraint(e, typ) ->
         fprintf ff "@[(%a: %a)@]" expression e ptype typ
      | Ematch { is_size; is_total; e; handlers } ->
         fprintf ff "@[<v>@[<hov 2>%smatch %s%a with@ @[%a@]@]@]"
           (if is_total then "total " else "")
           (if is_size then "size " else "")
           expression e (print_list_l (match_handler expression) """""")
           handlers
      | Epresent { handlers; default_opt } ->
         fprintf ff "@[<v>@[<hov 2>present@ @[%a@]@]@ @[%a@]@]"
           (print_list_l (present_handler (scondpat expression) expression)
	      """""") handlers
           (with_default expression) default_opt
      | Ereset(e_body, e) ->
         fprintf ff "@[<hov>reset@  @[%a@]@ every %a@]"
           expression e_body expression e
      | Efun(fe) ->
         fprintf ff "@[(%a)@]" funexp fe
      | Eassert a -> p_assert ff a
      | Eforloop({ for_size; for_kind; for_index; for_input; for_body;
                   for_env; for_resume }) ->
         let size ff for_size =
           Util.optional_unit (fun ff e -> fprintf ff "(%a)@ " expression e)
             ff for_size in
         fprintf ff
           "@[<hov 2>%a%a@,%a%a(%a) %a@ %a@ @[%a@]@ @]"
           kind_of_forloop for_kind
           for_resume_or_restart for_resume
           size for_size
           index_opt for_index
           input_list for_input
           print_env for_env
           for_exp for_body 
           for_exit_condition for_kind
    
    and p_assert ff { a_body; a_hidden_env; a_free_vars } =
      fprintf ff "@[<hov2>assert@ %a@]" expression a_body;
         print_hidden_env ff a_hidden_env;
         fprintf ff "@[<hov2>(* free variables:@ %a *)@]"
           Ident.S.fprint_t a_free_vars

    and result ff { r_desc } =
      match r_desc with
      | Exp(e) -> fprintf ff "@[<hov 2>->@ %a@]" expression e
      | Returns { b_vars; b_body; b_write; b_env } ->
         fprintf ff "@[<hov 2>returns@ (%a)@ @[%a@]@[%a@]@ @[%a@]@]"
           (vardec_list expression) b_vars
           print_env b_env
           print_writes b_write
           equation b_body
    
    and kind f_kind =
      match f_kind with
      | Kfun _ -> "fun "
      | Knode(k) ->
         (match k with | Kdiscrete -> "node " | Kcont -> "hybrid ")
    
    and funexp ff
          { f_vkind; f_kind; f_args; f_body; f_env; f_atomic;
            f_inline; f_hidden_env } =
      let vkind =
        match f_vkind with
        | Kconst -> "const " | Kstatic -> "static " | Kany -> "" in
      let is_atomic = if f_atomic then "atomic " else "" in
      let is_inline = if f_inline then "inline " else "" in
      fprintf ff "@[<hov 2>%s%s%s%s%a %a@ %a@]"
        is_inline is_atomic (kind f_kind) vkind arg_list f_args
        print_env f_env result f_body;
      fprintf ff "@[<hov0>%a@]" print_hidden_env f_hidden_env
    
    and arg_list ff a_list =
      print_list_r arg "" "" "" ff a_list
    
    and arg ff a = fprintf ff "(%a)" (vardec_list expression) a
    
    and operator ff op e_list =
      match op, e_list with
      | Eunarypre, [e] -> fprintf ff "@[<hov2>pre@ %a@]" expression e
      | Efby, [e1;e2] ->
         fprintf ff "@[<hov2>%a@ fby@ %a@]" expression e1 expression e2
      | Eminusgreater, [e1;e2] ->
         fprintf ff "@[<hov2>%a@ ->@ %a@]" expression e1 expression e2
      | Eifthenelse,[e1;e2;e3] ->
         fprintf ff "@[<hov2>(if@ %a then@ %a@ else@ %a)@]"
           expression e1 expression e2 expression e3
      | Eup { is_zero }, [e] ->
         fprintf ff "@[up%s %a@]" (if is_zero then "" else "b") expression e
      | Einitial, [] -> fprintf ff "init"  
      | Etest, [e] ->
         fprintf ff "@[? %a@]" expression e
      | Eatomic, [e] ->
         fprintf ff "@[<hov2>atomic@ %a@]" expression e
      | Eperiod, [e1; e2] ->
         fprintf ff 
           "@[<hov2>period@ %a(%a)@]" expression e1 expression e2
      | Eseq, [e1; e2] ->
         fprintf ff "@[<hov0>%a;@,%a@]" expression e1 expression e2
      | Erun(is_inline), [e1; e2] ->
         fprintf ff "@[<hov2>%srun@ %a@ %a@]"
           (if is_inline then "inline " else "") expression e1 expression e2
      | Ehorizon { is_zero }, [e] ->
         fprintf ff "@[<hov2>horizon%s@ %a@]" 
           (if is_zero then "" else "f") expression e
      | Edisc, [e] ->
         fprintf ff "@[<hov2>disc@ %a@]" expression e
      | Earray(op), l ->
         array_operator ff op l
      | _ -> assert false
    
    and array_operator ff op l =
      match op, l with
      | Earray_list, l ->
         Pp_tools.print_list_l expression "[|" ";" "|]" ff l
      | Econcat, [e1; e2] ->
         fprintf ff "@[<hov0>%a ++ @,%a@]" expression e1 expression e2
      | Eget, [e1; e2] ->
         fprintf ff "@[%a.(%a)@]" expression e1 expression e2
      | Eget_with_default, [e1; e2; e3] ->
         fprintf ff "@[<hov2>%a.(%a)@ default@ %a@]" 
           expression e1 expression e2 expression e3
      | Eslice, [e1; e2; e3] ->
         fprintf ff "@[<hov2>%a.@,(%a@ ..@ %a)@]" 
           expression e1 expression e2 expression e3
      | Eupdate, (e1 :: e2 :: i_list) ->
         (* [| e1 with i_list <- e2 |] *)
         fprintf ff "@[<hov 2>[|%a with@, %a <- %a|]@]"
           expression e1 (print_list_r expression "(" "," ")") i_list expression e2
      | Etranspose, [e] ->
         fprintf ff "@[%a.T@]" expression e
      | Ereverse, [e] ->
         fprintf ff "@[%a.R@]" expression e
      | Eflatten, [e] ->
         fprintf ff "@[%a.F@]" expression e
      | _ -> assert false
    
    and equation ff ({ eq_desc = desc } as eq) =
      print_eq_info ff eq;
      match desc with
      | EQeq(p, e) ->
         fprintf ff "@[<hov 2>%a =@ %a@]" pattern p expression e
      | EQsizefun { sf_id; sf_id_list; sf_e; sf_env } ->
         fprintf ff "@[<hov 2>%a%a@ %a =@ %a@]" name sf_id
           (print_list_l name "<<" "," ">>") sf_id_list
           print_env sf_env
           expression sf_e
      | EQder { id; e; e_opt; handlers = [] } ->
         fprintf ff "@[<hov 2>der %a =@ %a%a@]"
           name id expression e
           (Util.optional_unit
              (fun ff e -> fprintf ff " init %a " expression e)) e_opt
      | EQder { id; e; e_opt; handlers } ->
         fprintf ff "@[<hov 2>der %a =@ %a %a@ @[<hov 2>reset@ @[%a@]@]@]"
           name id expression e
           (Util.optional_unit
              (fun ff e -> fprintf ff "init %a " expression e)) e_opt
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
           ff (handlers, state_opt)
      | EQmatch { is_size; is_total; e; handlers } ->
         fprintf ff "@[<hov0>%smatch %s%a with@ @[%a@]@]"
           (if is_total then "total " else "")
           (if is_size then "size " else "")
           expression e (print_list_l (match_handler equation) """""") handlers
      | EQif { e; eq_true; eq_false } ->
         fprintf ff "@[<hov0>if %a@ then %a@ else %a@]"
           expression e equation eq_true equation eq_false
      | EQpresent { handlers; default_opt } ->
         fprintf ff "@[<hov0>present@ @[%a@]@ %a@]"
           (print_list_l
	      (present_handler (scondpat expression) equation) """""") handlers
           (with_default equation) default_opt
      | EQreset(eq, e) ->
         (* remove useless do/done when [eq] is a list of equations *)
         let equation ff ({ eq_desc } as eq) =
           match eq_desc with
           | EQand { ordered; eq_list } -> 
              and_equation ordered "" "" ff eq_list
           | _ -> equation ff eq in
         fprintf ff "@[<hov>reset@   @[%a@]@ @[<hov 2>every@ %a@]@]"
           equation eq expression e
      | EQlet(l_eq, eq) ->
         fprintf ff "@[<hov1>(%a in@ %a)@]" leq l_eq equation eq
      | EQlocal(b_eq) -> block_of_equation ff b_eq
      | EQand { ordered; eq_list } ->
         fprintf ff "@[<hov0>%a@]"
           (and_equation ordered "do " " done") eq_list
      | EQempty -> fprintf ff "()"
      | EQassert a -> p_assert ff a
      | EQforloop
        ({ for_size; for_kind; for_index; for_input; for_env; for_resume;
                    for_body = { for_out; for_block; for_out_env } }) ->
         let size ff for_size =
           Util.optional_unit (fun ff e -> fprintf ff "(%a)@ " expression e)
             ff for_size in
         let print_for_out ff l =
           let for_out ff
                 { desc = { for_name = x; for_out_name = o_opt;
                            for_init = i_opt } } =
             fprintf ff "@[%a%a%a@]" 
               name x (init expression) i_opt out o_opt in
           print_list_r for_out "" "," "" ff l in
         fprintf ff
           "@[<hov 2>%a%a%a%a@ (@[%a@])@ @[%a@]@ returns@ (%a)@ %a@ @[%a@,%a@]@ @]"
           kind_of_forloop for_kind
           for_resume_or_restart for_resume
           size for_size
           index_opt for_index
           input_list for_input
           print_env for_env
           print_for_out for_out
           print_env for_out_env
           block_of_equation for_block
           for_exit_condition for_kind       
    
    and and_equation ordered po pf ff eq_list =
      let a = if ordered then "; " else " and " in
      print_list_r equation po a pf ff eq_list
    
    (* print for loops *)
    and kind_of_forloop ff for_kind =
      match for_kind with
      | Kforeach -> fprintf ff "foreach "
      | Kforward _ -> fprintf ff "forward "
    
    and for_resume_or_restart ff for_resume =
      if for_resume then fprintf ff "resume "
    
    and for_exit_condition ff for_kind =
      let kind k =
        match k with
        | Ewhile -> "while" | Euntil -> "until" | Eunless -> "unless" in
      match for_kind with
      | Kforward(e_opt) ->
         Pp_tools.print_opt
           (fun ff { for_exit_kind; for_exit } ->
             fprintf ff "@[<hov 2>%s@ %a@ @]" (kind for_exit_kind)
               expression for_exit) ff e_opt
      | Kforeach -> ()
    
    and index_opt ff i_opt =
      let index ff id = fprintf ff "[%a]" name id in
      Util.optional_unit index ff i_opt
    
    and input_list ff l =
      let input ff { desc = desc } =
        match desc with
        | Einput {id; e; by } ->
           fprintf ff "@[%a in %a@]" name id expression e;
           Util.optional_unit
             (fun ff e -> fprintf ff " by %a " expression e) ff by
        | Eindex {id; e_left; e_right; dir } ->
           fprintf ff
	     "@[%a in %a %s %a@]"
             name id expression e_left (if dir then "to" else "downto")
             expression e_right in
      print_list_r input "" "," "" ff l
    
    and for_exp ff r =
      let for_returns ff for_vardec_list =
        let for_vardec ff { desc = { for_array; for_vardec } } =
          let rec print_array_of n ff x =
            if n = 0 then vardec expression ff x
            else fprintf ff "@[<hov 1>[|@,%a@,|]@]" (print_array_of (n-1)) x in
          print_array_of for_array ff for_vardec in
        print_list_r for_vardec "(" "" ")" ff for_vardec_list in
      match r with
      | Forexp { exp; default = d} ->
         fprintf ff "@[ do %a%a done@]" expression exp (default expression) d
      | Forreturns { r_returns; r_block; r_env } ->
         fprintf ff "@[<hov 2> returns@ (%a)@ @[%a@]@ @[%a@]@]"
           for_returns r_returns
           print_env r_env
           block_of_equation r_block
    
    
    and block_of_equation ff b_eq =
      block expression equation ff b_eq
    
    and leq ff { l_rec; l_kind; l_eq; l_env } =
      let s = if l_rec then " rec " else "" in
      fprintf ff "@[<v0>@[<hov2>let%a%s@ %a@ %a@]@]" 
        vkind l_kind s equation l_eq print_env l_env 
    
    and leqs ff l = print_list_r_empty leq "" "in" "in " ff l
    
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
    
    let open_module ff n =
      fprintf ff "@[open %a@]@." shortname n
    
    let interface ff { desc } =
      match desc with
      | Einter_open(n) -> open_module ff n
      | Einter_typedecl { name; ty_params; ty_decl } ->
         fprintf ff "@[<v 2>type %a%s %a@]@."
           print_type_params ty_params name type_decl ty_decl
      | Einter_constdecl { name; const; ty; info } ->
         let print_n ff n = fprintf ff "%s" n in
         fprintf ff "@[<v 2>%s %s : %a%a@]@."
           (if const then "val const" else "val") name
           ptype ty (print_list_r print_n "=[" " " "]") info
    
    let interface_list ff int_list =
      List.iter (interface ff) int_list

    let implementation ff { desc } =
      match desc with
      | Eopen(n) -> open_module ff n
      | Etypedecl { name; ty_params; ty_decl } ->
         fprintf ff "@[<v 2>type %a%s %a@]@."
           print_type_params ty_params name type_decl ty_decl
      | Eletdecl { d_names; d_leq } ->
         let print_d_names ff d_names =
           List.iter
             (fun (n, id) ->
               fprintf ff
                 "@[<v0>(* globally defined name *)@ let %s = %a@.@]"
                 n name id) d_names in
         (* print the set of equations and the list of globally defined names *)
         fprintf ff "@[<v0>%a@ %a@]" leq d_leq print_d_names d_names         
    
    let program ff { p_impl_list; p_index } = 
      fprintf ff "Index number = %d@." p_index;
      List.iter (implementation ff) p_impl_list
  end
