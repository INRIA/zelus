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

(* translation from zelus code to obc *)
(* applied to normalized and scheduled code *)
open Misc
open Ident
open Global
open Deftypes
open Obc
module Printer = Printer.Make(Typinfo)

(* is-it a mutable value? Only vectors are considered at the moment *)
let rec is_mutable { t_desc = desc } =
  match desc with
  | Tvec _ -> true
  | Tlink(link) -> is_mutable link
  | _ -> false
           
(* The translation uses an environment to store information about identifiers *)
type env = entry Env.t (* the symbol table *)
 and entry =
   { e_typ: Deftypes.typ;
     e_sort: sort;
     e_size: loop_path; (* [e.(i_1)...(i_n)] *)
   }
 and sort =
   | In of exp
   (* the variable [x] is implemented by [e.(i_1)...(i_n)]; e.g., [x in e] *)
   | Out of Ident.t * Deftypes.tsort
   (* the variable [x] is stored into [y.(i_1)...(i_n); e.g. [x out y]] *)

 and loop_path = Ident.t list
			 
let fprint ff (env: entry Env.t) =
  let fprint_entry ff { e_typ = ty; e_sort = sort; e_size = size } =
    Format.fprintf ff "@[{ typ = %a;@,size = %a}@]"
		   Ptypes.output_type ty
		   (Pp_tools.print_list_r Printer.name "[" "," "]") size in
  Ident.Env.fprint_t fprint_entry ff env
		   

type context =
  { init: Obc.exp; (* sequence of initializations for [mem] *)
    mem: mentry Parseq.t; (* set of state variables *)
    instances: ientry Parseq.t; (* set of instances *)
    reset: Obc.exp; (* sequence of equations for resetting the block *)
  }

let empty_context =
  { mem = Parseq.empty; init = Oaux.void;
    instances = Parseq.empty;
    reset = Oaux.void }

let seq { mem = m1; init = i1; instances = j1; reset = r1 } 
	{ mem = m2; init = i2; instances = j2; reset = r2 } =
  { mem = Parseq.seq m1 m2; init = Oaux.seq i1 i2; instances = Parseq.par j1 j2;
    reset = Oaux.seq r1 r2 }

let empty_path = []

(* Look for an entry in the environment *)
let entry_of n env =
  try
    Env.find n env
  with Not_found ->
    Misc.internal_error "Translate: unbound variable" Printer.name n

(** Translation of immediate values *)
let immediate = function
  | Zelus.Eint(i) -> Eint(i)
  | Zelus.Efloat(f) -> Efloat(f)
  | Zelus.Ebool(b) -> Ebool(b)
  | Zelus.Echar(c) -> Echar(c)
  | Zelus.Estring(s) -> Estring(s)
  | Zelus.Evoid -> Evoid

(* read/write of a state variable. *)
let state is_read n k =
  match k with
  | None -> Eleft_state_name(n)
  | Some(k) ->
     match k with
     | Deftypes.Cont ->
	Eleft_state_primitive_access (Eleft_state_name(n), Epos)
     | Deftypes.Zero ->
	Eleft_state_primitive_access
	  (Eleft_state_name(n), if is_read then Ezero_in else Ezero_out)
     | Deftypes.Horizon | Deftypes.Period
     | Deftypes.Encore | Deftypes.Major | Deftypes.Time -> Eleft_state_name(n)

(* index in an array *)
let rec index e =
  function
  | [] -> e
  | ei :: ei_list ->
     Eget { e = index e ei_list; index = Evar { is_mutable = false;
                                                id = ei } }

let rec left_value_index lv =
  function
  | [] -> lv
  | ei :: ei_list ->
     Eleft_index(left_value_index lv ei_list,
                 Evar { is_mutable = false; id = ei })

let rec left_state_value_index lv = function
  | [] -> lv
  | ei :: ei_list ->
     Eleft_state_index(left_state_value_index lv ei_list,
                       Evar { is_mutable = false; id = ei })
						      
(* read of a variable *)
let var { e_sort; e_typ; e_size = ei_list } =
  match e_sort with
  | In(e) -> index e ei_list
  | Out(n, sort) ->
     match sort with
     | Sort_val -> index (Evar { is_mutable = false; id = n }) ei_list
     | Sort_var ->
        let i = is_mutable e_typ in
        index (Evar { is_mutable = i; id = n }) ei_list
     | Sort_mem { m_mkind } ->
        Estate(left_state_value_index (state true n m_mkind) ei_list)

(* Make an assignment according to the sort of a variable [n] *)
let assign n { e_sort; e_size = ei_list } e =
  match e_sort with
  | In _ -> (* this case should not happend *) 
     Misc.internal_error "Translate: assign" Printer.name n
  | Out(n, sort) ->
     match sort with
     | Sort_val -> 
        (* this case should not happend *) 
        Misc.internal_error "Translate: assign (wrong sort)" Printer.name n
     | Sort_var -> Eassign(left_value_index (Eleft_name n) ei_list, e)
     | Sort_mem { m_mkind } ->
	Eassign_state(left_state_value_index (state false n m_mkind) ei_list, e)

(* Generate the code for a definition *)
(* [k] is the continuation. Either a local def [let id = e in k] or *)
(* an assignment, to a shared or state variable [self.id <- e; k] *)
let def n { e_typ; e_sort; e_size = ei_list } e k =
  match e_sort with
  | In _ -> (* this case should not happend *) 
     Misc.internal_error "Translate: def" Printer.name n
  | Out(id, sort) ->
     match sort with
     | Sort_val ->
        Elet(Evarpat { id; ty = Interface.type_expression_of_typ e_typ }, e, k)
     | Sort_var ->
	Oaux.seq (Eassign(left_value_index (Eleft_name id) ei_list, e)) k
     | Sort_mem { m_mkind } ->
	Oaux.seq
	  (Eassign_state(left_state_value_index
			   (state false id m_mkind) ei_list, e)) k
	  
(* Generate the code for [der x = e] *)
let der n { e_sort; e_size = ei_list } e k =
  match e_sort with
  | In _ -> 
     (* this case should not happend *) 
     Misc.internal_error "Translate: der" Printer.name n
  | Out(n, sort) ->
     Oaux.seq (Eassign_state(left_state_value_index
			       (Eleft_state_primitive_access
				  (Eleft_state_name(n), Eder)) ei_list,
                             e)) k
       
(* Generate an if/then *)
let ifthen r_e i_code = Eifthenelse(r_e, i_code, Oaux.void)
				   
(* Generate a for loop *)
let for_loop dir ix e1 e2 e_body =
  match e_body with
  | Econst (Evoid) | Esequence [] -> e_body
  | _ -> Efor { index = ix; dir = dir; left = e1; right = e2; e = e_body }

(* Generate the code for the definition of a value *)
let letpat p e k = Elet(p, e, k)

(* Generate the code for initializing shared variables *)
let rec letvar l k =
  match l with
  | [] -> k
  | (id, is_mutable, ty, e_opt) :: l ->
     Eletvar { id; is_mutable; ty; e_opt; e = letvar l k }
				  
   
let out_of n env =
  let { e_typ = ty; e_sort = sort; e_size = ix_list } = entry_of n env in
  match sort with
  | In _ -> (* this case should not happend *)
     Misc.internal_error "Translate: out_of" Printer.name n
  | Out(x, sort) -> x, ty, sort, ix_list

(* Translate size expressions *)
let rec exp_of_sizetype si =
  let open Defsizes in
  match si with
  | Sint(i) -> Oaux.int_const i
  | Svar(n) -> Evar { is_mutable = false; id = n }
  | Sfrac { num; denom } ->
     Oaux.div (exp_of_sizetype num) (Oaux.int_const denom)
  | Sop(op, s1, s2) ->
     let e1 = exp_of_sizetype s1 in
     let e2 = exp_of_sizetype s2 in
     match op with
     | Splus -> Oaux.plus e1 e2
     | Sminus -> Oaux.minus e1 e2
     | Smult -> Oaux.mult e1 e2

(* makes an initial value from a type. returns None when it fails *)
let choose env ty =
  let tuple l = Etuple(l) in
  let efalse = Econst(Ebool(false)) in
  let echar0 = Econst(Echar('a')) in
  (* on purpose, take an initial value different from zero *)
  let ezero = Econst(Eint(-1)) in
  let efzero = Econst(Efloat(-1.0)) in
  let estring0 = Econst(Estring("")) in
  let evoid = Econst(Evoid) in
  let eany = Econst(Eany) in
  let vec e size = Evec { e; size } in
  let rec value_from_deftype id =
    try
      let { info = { type_desc = ty_c } } = 
        Modules.find_type (Lident.Modname(id)) in
      match ty_c with
      | Variant_type(g_list) -> value_from_variant_list g_list
      | Abstract_type -> eany
      | Record_type(l_list) ->
          Erecord(
	    List.map 
              (fun { qualid = qualid; info = { label_res = ty } } -> 
                 { label = Lident.Modname(qualid); arg = value ty }) l_list)
      | Abbrev(_, ty) -> value ty
    with
      | Not_found -> eany
  and value ty =
    match ty.t_desc with
    | Tvar -> eany
    | Tproduct(ty_l) -> tuple (List.map value ty_l)
    | Tarrow _ | Tsizefun _ -> eany
    | Tvec(ty, si) -> vec (value ty) (exp_of_sizetype si)
    | Tconstr(id, _, _) ->
       if id = Initial.int_ident then ezero
       else if id = Initial.bool_ident then efalse
       else if id = Initial.char_ident then echar0
       else if id = Initial.float_ident then efzero
       else if id = Initial.string_ident then estring0
       else if id = Initial.unit_ident then evoid
       else if id = Initial.zero_ident then efalse
       else 
         (* try to find a value from its type definition *)
         (* we do not consider type instantiation here *)
         value_from_deftype id 
    | Tlink(link) -> value link
  and value_from_variant_list g_list =
    let rec findrec g_list =
      match g_list with
      | [] -> raise Not_found
      | { qualid = qualid; info = { constr_arity = arity } } :: g_list ->
          if arity = 0 then Econstr0 { lname = Lident.Modname(qualid) }
          else findrec g_list in
    try
      (* look for a constructor with arity 0 *)
      findrec g_list
    with
    | Not_found ->
        (* otherwise, pick one *)
        let { qualid = qualid; info = { constr_arg = ty_list } } =
                                      List.hd g_list in
        Econstr1 { lname = Lident.Modname(qualid);
                   arg_list = List.map value ty_list } in
  Some(value ty)

(* Computes a default value *)
let default env ty v_opt =
  match v_opt with
  | None -> choose env ty
  | Some(v) -> Some(Econst v)
			
(* Extension of an environment *)
(* The access to a state variable [x] is turned into the access on an *)
(* array access x.(i1)...(in) if loop_path = [i1;...;in] *)
let append loop_path l_env env =
  (* add a memory variable for every state variable in [l_env] *)
  (* and a [letvar] declaration for every shared variable *)
  let addrec n { t_sort; t_tys = { typ_body } } (env_acc, mem_acc, var_acc) =
    match t_sort with
      | Sort_val | Sort_mem { m_mkind = None; m_last = false; m_init = No } ->
	 (* if [n] is a memory but no [last] nor [init] is defined *)
         (* it is treated as a local variable *)
         Env.add n { e_typ = typ_body; e_sort = Out(n, Sort_val); e_size = [] }
           env_acc,
	 mem_acc, var_acc
      | Sort_var ->
	 Env.add n { e_typ = typ_body; e_sort = Out(n, Sort_var); e_size = [] }
           env_acc,
	 mem_acc,
         (n, is_mutable typ_body, typ_body, default env typ_body None)
         :: var_acc
      | Sort_mem { m_mkind } ->
	 Env.add n
	   { e_typ = typ_body; e_sort = Out(n, t_sort); e_size = loop_path }
           env_acc,
	 Parseq.cons
           { m_name = n; m_value = choose env typ_body; m_typ = typ_body;
	     m_kind = m_mkind; m_size = [] } mem_acc,
	 var_acc in
  let env_acc, mem_acc, var_acc = Env.fold addrec l_env (env, Parseq.empty, []) in
  env_acc, mem_acc, var_acc


(* Translation of a stateful function application [f se1 ... sen e] *)
(* if [loop_path = [i1;...;ik]
 * instance o = f se1 ... sen
 * call o.(i1)...(ik).step(e)
 * reset with o.(i1)...(ik).reset *)
let apply k env loop_path context e e_list =
  match k with
  | Deftypes.Tfun _ -> Eapp { f = e; arg_list = e_list }, context
  | Deftypes.Tnode _ ->
     (* the first [n-1] arguments are static *)
     let se_list, arg = Util.firsts e_list in
     let f_opt = match e with | Eglobal { lname } -> Some lname | _ -> None in
     let loop_path =
       List.map (fun ix -> Evar { is_mutable = false; id = ix }) loop_path in
     (* create an instance *)
     let o = Ident.fresh "i" in
     let j_context = { i_name = o; i_machine = e; i_kind = k;
		    i_params = se_list; i_size = [] } in
     let reset_context =
       Emethodcall({ met_machine = f_opt; met_name = Oaux.reset;
		     met_instance = Some(o, loop_path); met_args = [] }) in
     let step =
       Emethodcall({ met_machine = f_opt; met_name = Oaux.step;
		     met_instance = Some(o, loop_path); met_args = [arg] }) in
     step,
     { context with instances = Parseq.cons j_context context.instances;
                 reset = Oaux.seq reset_context context.reset }

(* Define a function or a machine according to a kind [k] *)
let machine f k pat_list { mem; instances; reset } e ty_res =
  let k = Interface.kindtype k in
  match k with
  | Deftypes.Tfun _ -> Efun { pat_list; e }
  | Deftypes.Tnode _ ->
    (* the [n-1] parameters are static *)
    let pat_list, p = Util.firsts pat_list in
    let body =
      { ma_name = f;
        ma_kind = k;
	ma_params = pat_list;
	ma_initialize = None;
	ma_memories = Parseq.list [] mem;
	ma_instances = Parseq.list [] instances;
	ma_methods = 
	  [ { me_name = Oaux.reset; me_params = []; me_body = reset;
              me_typ = Initial.typ_unit };
	    { me_name = Oaux.step; me_params = [p]; me_body = e;
              me_typ = ty_res } ] } in
    Emachine(body)

let add_mem_vars_to_context mem_acc var_acc (e, ({ mem } as context)) =
  letvar var_acc e, { context with mem = Parseq.seq mem_acc mem } 

(* Patterns *)
let rec pattern { Zelus.pat_desc = desc; Zelus.pat_info = info } =
  let ty = Typinfo.get_type info in
  match desc with
  | Zelus.Ewildpat -> Ewildpat
  | Zelus.Econstpat(im) -> Econstpat(immediate im)
  | Zelus.Econstr0pat(c0) -> Econstr0pat(c0)
  | Zelus.Econstr1pat(c1, p_list) ->
     Econstr1pat(c1, List.map pattern p_list)
  | Zelus.Etuplepat(p_list) -> Etuplepat(List.map pattern p_list)
  | Zelus.Evarpat(id) -> 
     Evarpat { id; ty = Interface.type_expression_of_typ ty }
  | Zelus.Erecordpat(label_pat_list) ->
     Erecordpat
       (List.map
          (fun { Zelus.label; Zelus.arg } -> { label; arg = pattern arg })
	  label_pat_list)
  | Zelus.Etypeconstraintpat(p, ty) ->
     Etypeconstraintpat(pattern p, ty)
  | Zelus.Ealiaspat(p, n) -> Ealiaspat(pattern p, n)
  | Zelus.Eorpat(p1, p2) -> Eorpat(pattern p1, pattern p2)
  | Zelus.Earraypat(p_list) ->
     Econstr1pat(Lident.Modname(Initial.array_list_ident), List.map pattern p_list)

(* Translation of a math/with handler. *)
let match_handlers body env loop_path context p_h_list =
  let body context { Zelus.m_pat; Zelus.m_body; Zelus.m_env } =
    let env, mem_acc, var_acc = append loop_path m_env env in
    let step, context = body env loop_path m_body context in
    { m_pat = pattern m_pat; m_body = letvar var_acc step }, context in
  Util.mapfold body context p_h_list

(* Translation of expressions under an environment [env] *)
(* [context] is the context already generated *)
(* [expression env e context = e', context'] where [context'] extends *)
(* [context] with new *)
(* memory, instantiation and reset. *)
(* [loop_path = [i1;...;in]] is the loop path if [e] appears in *)
(* a nested loop forall in ... forall i1 do ... e ... *)
let rec expression env loop_path context { Zelus.e_desc } =
  match e_desc with
  | Zelus.Econst(i) -> Econst(immediate i), context
  | Zelus.Evar(n)
    | Zelus.Elast { id = n } ->
     var (entry_of n env), context
  | Zelus.Eglobal { lname = ln } ->
     Eglobal { lname = ln }, context
  | Zelus.Econstr0 { lname } ->
     Econstr0 { lname }, context
  | Zelus.Econstr1 { lname; arg_list } ->
     let arg_list, context =
       Util.mapfold (expression env loop_path) context arg_list in
     Econstr1 { lname; arg_list }, context
  | Zelus.Etuple(e_list) ->
     let e_list, context =
       Util.mapfold (expression env loop_path) context e_list in
     Etuple(e_list), context
  | Zelus.Erecord(label_e_list) ->
     let label_e_list, context =
       Util.mapfold
	 (fun context { Zelus.label; Zelus.arg } ->
           let arg, context = expression env loop_path context arg in
	   { label; arg }, context) context label_e_list in
     Erecord(label_e_list), context
  | Zelus.Erecord_access { Zelus.label; Zelus.arg } ->
     let arg, context =
       expression env loop_path context arg in
     Erecord_access { label; arg }, context
  | Zelus.Erecord_with(e_record, label_e_list) ->
     let e_record, context =
       expression env loop_path context e_record in
     let label_e_list, context =
       Util.mapfold
	 (fun context { Zelus.label; Zelus.arg } ->
           let arg, context = expression env loop_path context arg in
	   { label; arg }, context) context label_e_list in
     Erecord_with(e_record, label_e_list), context
  | Zelus.Etypeconstraint(e, ty_expression) ->
     let e, context = expression env loop_path context e in
     Etypeconstraint(e, ty_expression), context
  | Zelus.Eop(Zelus.Eup _, [e]) ->
     (* implement the zero-crossing up(x) by up(if x >=0 then 1 else -1) *)
     let e = if !Misc.zsign then Aux.sgn e else e in 
     expression env loop_path context e
  | Zelus.Eop(Zelus.Ehorizon _, [e]) ->
     expression env loop_path context e
  | Zelus.Eop(Zelus.Eifthenelse, [e1; e2; e3]) ->
     let e1, context = expression env loop_path context e1 in
     let e2, context = expression env loop_path context e2 in
     let e3, context = expression env loop_path context e3 in
     Eifthenelse(e1, e2, e3), context
  | Zelus.Eop(Zelus.Earray(Eget), [e1; e2]) ->
     let e1, context = expression env loop_path context e1 in
     let e2, context = expression env loop_path context e2 in
     Eget { e = e1; index = e2 }, context
  | Zelus.Eop(Zelus.Earray(Eupdate), [e1; i; e2]) ->
     let ty = Typinfo.get_type e1.e_info in
     let _, se = Types.filter_vec ty in
     let se = exp_of_sizetype se in
     let e1, context = expression env loop_path context e1 in
     let i, context = expression env loop_path context i in
     let e2, context = expression env loop_path context e2 in
     Eupdate { e = e1; index = i; arg = e2; size = se }, context
  | Zelus.Eop(Zelus.Earray(Eslice), [e1; e2; e]) ->
     let e1, context = expression env loop_path context e1 in
     let e2, context = expression env loop_path context e2 in
     let e, context = expression env loop_path context e in
     Eslice { e; left = e1; right = e2 }, context
  | Zelus.Eop(Zelus.Earray(Econcat), [e1; e2]) -> 
     let ty1 = Typinfo.get_type e1.e_info in
     let ty2 = Typinfo.get_type e2.e_info in
     let _, s1 = Types.filter_vec ty1 in
     let _, s2 = Types.filter_vec ty2 in
     let s1 = exp_of_sizetype s1 in
     let s2 = exp_of_sizetype s2 in
     let e1, context = expression env loop_path context e1 in
     let e2, context = expression env loop_path context e2 in
     Econcat { left = e1; left_size = s1; right = e2; right_size = s2 }, context
  | Zelus.Eop(Zelus.Eatomic, [e]) ->
     expression env loop_path context e  
  | Zelus.Eop(Eseq, [e1; e2]) ->
     let e1, context  = expression env loop_path context e1 in
     let e2, context = expression env loop_path context e2 in
     Oaux.seq e1 e2, context
  | Zelus.Eapp { f; arg_list } ->
     (* make an application *)
     let make_app f arg_list =
       match arg_list with | [] -> f | _ -> Eapp { f; arg_list } in
     let ty = Typinfo.get_type f.e_info in
     (* compute the sequence of static arguments and non static ones *)
     let se_list, ne_list, ty_res = 
       Types.split_arguments ty arg_list in
     let f, context = expression env loop_path context f in
     let se_list, context =
       Util.mapfold (expression env loop_path) context se_list in
     let ne_list, context =
       Util.mapfold (expression env loop_path) context ne_list in
     let e_fun = make_app f se_list in
     let e_fun, context = match ne_list with
       | [] -> e_fun, context
       | _ -> let k = Types.kind_of_funtype ty_res in
	      apply k env loop_path context e_fun ne_list in
     e_fun, context
  | Zelus.Efun { Zelus.f_kind = k; Zelus.f_args = arg_list;
		 Zelus.f_body = r; Zelus.f_env = f_env; Zelus.f_hidden_env } ->
     let ty = Typinfo.get_type r.r_info in
     let pat_list = List.map arg arg_list in
     let f_env = Env.append f_hidden_env f_env in
     let env, mem_acc, var_acc = append empty_path f_env Env.empty in
     let e, context_body = result env r in
     let e, context_body =
       add_mem_vars_to_context mem_acc var_acc (e, context_body) in
     let f = Ident.fresh "machine" in
     machine f k pat_list context_body e ty, context
  | Zelus.Ereset(e, r_e) ->
     let r_e, context = expression env loop_path context r_e in
     let e, ({ init } as context_e) = expression env loop_path empty_context e in
     (* execute the initialization context when [r_e] is true *)
     Oaux.seq (ifthen r_e init) e,
     seq context context_e    
  | Esizeapp _ -> Misc.not_yet_implemented "sizeapp"
  | Eforloop _ -> Misc.not_yet_implemented "for loops"
  | Zelus.Eassert(e) ->
     let e, context = expression env loop_path context e in
     Eassert(e), context
  | Zelus.Elet(l, e) ->
     leq_in_e env loop_path l context e
  | Zelus.Elocal(b, e) ->
     block_in_e env loop_path b context e
  | Zelus.Ematch { e; handlers } ->
     let e, context = expression env loop_path context e in
     let handlers, context =
       match_handlers
         (fun env loop_path e context -> expression env loop_path context e)
         env loop_path context handlers in
     Ematch(e, handlers), context
  | Zelus.Eop(Eperiod, _)  | Zelus.Eop _ | Zelus.Epresent _ ->
     (* these last constructions have been rewritten in previous steps *)
     assert false

and arg a_list =
  match a_list with | [] -> Ewildpat | _ -> Etuplepat (List.map vardec a_list)

and vardec { Zelus.var_name = id; Zelus.var_info = info } =
  let ty = Typinfo.get_type info in
  Evarpat { id; ty = Interface.type_expression_of_typ ty }

and result env { Zelus.r_desc } =
  match r_desc with
  | Exp(e) -> expression env empty_path empty_context e
  | Returns _ ->
     (* the returns handler has been eliminated in previous passes *)
     assert false

(* Translation of equations. They are traversed in reverse order *)
(* from the last one to the first one *)
(* [step,context] is the already generated context. The generated *)
(* context for [eq] is *)
(* executed before [step] *)
and equation env loop_path { Zelus.eq_desc = desc } (step, context) =
  match desc with
  | Zelus.EQeq({ Zelus.pat_desc = Zelus.Evarpat(n) }, e) ->
     let e, context = expression env loop_path context e in
     def n (entry_of n env) e step, context
  | Zelus.EQeq(p, e) ->
     let e, context = expression env loop_path context e in
     letpat (pattern p) e step, context
  | Zelus.EQder { id; e; e_opt = None; handlers = [] } ->
     let e, context = expression env loop_path context e in
     der id (entry_of id env) e step, context
  | Zelus.EQder _ -> assert false
  | Zelus.EQmatch { e; handlers } ->
     let e, context = expression env loop_path context e in
     let handlers, context =
       match_handlers
         (fun env loop_path eq context ->
           equation env loop_path eq (Oaux.void, context))
         env loop_path context handlers in
     Oaux.seq (Ematch(e, handlers)) step, context
  | Zelus.EQreset({ Zelus.eq_desc = Zelus.EQinit(x, e) }, r_e)
       when not (Types.static e) ->
     let r_e, context = expression env loop_path context r_e in
     let e, ({ init } as e_context) = expression env loop_path empty_context e in
     Oaux.seq
       (ifthen r_e (Oaux.seq (assign x (entry_of x env) e) init)) step,
     seq context e_context
  | Zelus.EQreset(eq, r_e) ->
     let r_e, context = expression env loop_path context r_e in
     let e, ({ init } as context_eq) =
       equation env loop_path eq (Oaux.void, empty_context) in
     (* execute the initialization context when [r_e] is true *)
     Oaux.seq (ifthen r_e init) e, seq context context_eq
  | Zelus.EQinit(x, e) ->
     let e_c, context = expression env loop_path context e in
     let x_equal_e = assign x (entry_of x env) e_c in
     (* initialization of a state variable with a static value *)
     if Types.static e
     then step,
          seq { empty_context with init = x_equal_e; reset = x_equal_e } context
     else Oaux.seq x_equal_e step, context
  | Zelus.EQempty -> step, context
  | Zelus.EQand { ordered = true; eq_list } ->
     equation_list env loop_path eq_list (step, context)
  | Zelus.EQand _ -> assert false
  | Zelus.EQlocal(b) ->
     block env loop_path b (step, context)
  | Zelus.EQlet(l, eq_let) -> 
     leq_in_eq env loop_path l eq_let (step, context)
  | Zelus.EQif { e; eq_true; eq_false } ->
     let e, context = expression env loop_path context e in
     let e_true, context =
       equation env loop_path eq_true (Oaux.void, context) in
     let e_false, context =
       equation env loop_path eq_false (Oaux.void, context) in
     Oaux.seq (Oaux.ifthenelse e e_true e_false) step, context
  | Zelus.EQassert(e) ->
     let e, context = expression env loop_path context e in
     Oaux.seq (Eassert(e)) step, context
  | Zelus.EQemit _ | Zelus.EQautomaton _ | Zelus.EQpresent _ -> assert false
  | Zelus.EQforloop _ -> Misc.not_yet_implemented "for loops"
  | Zelus.EQsizefun _ -> assert false
  
and sizefun_list env s_list =
  List.map (sizefun env) s_list

and sizefun env { Zelus.sf_id; Zelus.sf_id_list; Zelus.sf_e } =
  let sf_e, context = expression env empty_path empty_context sf_e in
  { sf_id; sf_id_list; sf_e }

and equation_list env loop_path eq_list (step, context) =
  List.fold_right
    (fun eq (step, context) ->
      equation env loop_path eq (step, context)
    ) eq_list
    (step, context)

and leq_in_eq env loop_path { Zelus.l_eq; Zelus.l_env } eq_let (step, context) =
  let env, mem_acc, var_acc = append loop_path l_env env in
  let e, context = equation env loop_path eq_let (step, context) in
  let e, context =
    equation env loop_path l_eq (e, context) in
  add_mem_vars_to_context mem_acc var_acc (e, context)

and leq_in_e env loop_path { Zelus.l_eq; Zelus.l_env } context e =
  let env, mem_acc, var_acc = append loop_path l_env env in
  let e, context = expression env loop_path context e in
  let e, context =
    equation env loop_path l_eq (e, context) in
  add_mem_vars_to_context mem_acc var_acc (e, context)

and block env loop_path { Zelus.b_body; Zelus.b_env } (step, context) =
  let env, mem_acc, var_acc = append loop_path b_env env in
  let step, context = equation env loop_path b_body (step, context) in
  add_mem_vars_to_context mem_acc var_acc (step, context)

and block_in_e env loop_path { Zelus.b_body; Zelus.b_env } context e =
  let env, mem_acc, var_acc = append loop_path b_env env in
  let step, context = expression env loop_path context e in
  let step, context = equation env loop_path b_body (step, context) in
  add_mem_vars_to_context mem_acc var_acc (step, context)

(* translate a type declaration *)
let rec type_decl { Zelus.desc } =
  match desc with
  | Zelus.Eabstract_type -> Eabstract_type
  | Zelus.Eabbrev(ty) -> Eabbrev(ty)
  | Zelus.Evariant_type(c_list) ->
     Evariant_type(List.map constr_decl c_list)
  | Zelus.Erecord_type(label_ty_list) ->
     Erecord_type(List.map (fun (l, ty) -> (false, l, ty)) label_ty_list)

and constr_decl { Zelus.desc } =
  match desc with
  | Zelus.Econstr0decl(n) -> Econstr0decl(n)
  | Zelus.Econstr1decl(n, ty_list) -> Econstr1decl(n, ty_list)

let tuple_of_dnames d_names =
  let l = List.map (fun (_, id) -> Aux.var id) d_names in
  match l with
  | [] -> Aux.evoid | [v] -> v | l -> Aux.tuple l

(* Translation of a declaration *)
let implementation { Zelus.desc } =
  match desc with
  | Zelus.Eopen(n) -> Eopen(n)
  | Zelus.Etypedecl { name; ty_params; ty_decl } ->
     Etypedecl [name, ty_params, type_decl ty_decl]
  | Zelus.Eletdecl { d_names; d_leq } ->
     (* [let eq] with [id1,...,idn] the set of defined names *)
     (* and [f1 = id1;...;fn = id] the set of visible global names *)
     (* compile [let eq in (id1,...,idn)] into an expression [e] *)
     (* returns [let f1,...,fn = e] *)
     let n_list = List.map (fun (name, _) -> name) d_names in
     let ret = tuple_of_dnames d_names in
     (* There should be no memory allocated by [eq] *)
     let e, _ = leq_in_e Env.empty empty_path d_leq empty_context ret in
     Eletdef [n_list, e]
	     
let program { Zelus.p_impl_list } =
  { p_impl_list = Util.iter implementation p_impl_list }
