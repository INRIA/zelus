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
module Printer = Printer.Make(Ptypinfo)

(* is-it a mutable value? Only vectors are considered at the moment *)
let rec is_mutable { t_desc = desc } =
  match desc with
  | Tvec _ -> true
  | Tlink(link) -> is_mutable link
  | _ -> false
           
(* Symbol table that stores information about identifiers *)
type entry =
      { e_typ: Deftypes.typ;
        e_sort: sort;
        e_size: loop_path; (* [e.(i_1)...(i_n)] *)
      }
and sort =
  | In of exp
  (* the variable [x] is implemented by [e.(i_1)...(i_n)]; e.g., [x in e] *)
  | Out of
      { y: Ident.t;
        tsort: Deftypes.tsort;
        self: Ident.t option }
(* the variable [x] is stored into [y.(i_1)...(i_n); e.g. [x out y]] *)
(* if [y] is a state variable, it is represented as self.id where [self] *)
(* is the name of the state for the machine in which [y] is defined *)
(* [self] is the name of the memory state*)

(* A variable [x] inside [n] nested parallel loops *)
(* is represented as an n-dimension array. The access to [x] *)
(* is represented as x.(i1)...(in)] *)
and loop_path = Ident.t list
    
type env =
  { env: entry Env.t; (* symbol table *)
    self: Ident.t option; (* current name for the state *)
    (* the default memory state variable is [self] *)
  }

let empty_env = { env = Env.empty; self = None }

let fprint ff { env; self } =
  let fprint_env ff env =
    let fprint_entry ff { e_typ = ty; e_sort = sort; e_size = size } =
      Format.fprintf ff "@[{ typ = %a;@,size = %a}@]"
	Ptypes.ptype ty
	(Pp_tools.print_list_r Printer.name "[" "," "]") size in
    Ident.Env.fprint_t fprint_entry ff env in
  Format.fprintf ff
    "@[<hov 2>{ env = %a;@ self = %a}@]"
    fprint_env env
    (Pp_tools.print_opt Ident.fprint_t) self

type code =
  { init: Obc.exp; (* sequence of initializations for [mem] *)
    mem: mentry Parseq.t; (* set of state variables *)
    instances: ientry Parseq.t; (* set of instances *)
    reset: Obc.exp; (* code to reset the memory state *)
    (* transparent assertions (for hybrid models) *)
    assertions: machine Parseq.t; }

let empty_code =
  { mem = Parseq.empty; init = Oaux.void;
    instances = Parseq.empty;
    reset = Oaux.void;
    assertions = Parseq.empty }

let seq { mem = m1; init = i1; instances = j1; reset = r1; assertions = a1 } 
	{ mem = m2; init = i2; instances = j2; reset = r2; assertions = a2 } =
  { mem = Parseq.seq m1 m2; init = Oaux.seq i1 i2; instances = Parseq.par j1 j2;
    reset = Oaux.seq r1 r2; assertions = Parseq.par a1 a2 }

let empty_loop_path = []

(* Look for an entry in the environment *)
let entry_of n { env } =
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
let state self is_read name k =
  match k with
  | None -> Eleft_state_name { self; name }
  | Some(k) ->
     match k with
     | Deftypes.Cont ->
	Eleft_state_primitive_access
          (Eleft_state_name { self; name }, Epos)
     | Deftypes.Zero ->
	Eleft_state_primitive_access
	  (Eleft_state_name { self; name },
           if is_read then Ezero_in else Ezero_out)
     | Deftypes.Horizon | Deftypes.Period
       | Deftypes.Encore | Deftypes.Major | Deftypes.Time ->
        Eleft_state_name { self; name }

(* index in an array *)
let rec index e =
  function
  | [] -> e
  | ei :: ei_list ->
     Eget { e = index e ei_list; index = Oaux.local ei }

let rec left_value_index lv =
  function
  | [] -> lv
  | ei :: ei_list ->
     Eleft_index(left_value_index lv ei_list, Oaux.local ei)

let rec left_state_value_index lv = function
  | [] -> lv
  | ei :: ei_list ->
     Eleft_state_index(left_state_value_index lv ei_list, Oaux.local ei)
						      
(* read of a variable *)
let var { e_sort; e_typ; e_size = ei_list } =
  match e_sort with
  | In(e) -> index e ei_list
  | Out { y; tsort; self } ->
     match tsort with
     | Sort_val -> index (Oaux.local y) ei_list
     | Sort_var ->
        let i = is_mutable e_typ in
        index (Evar { is_mutable = i; id = y }) ei_list
     | Sort_mem { m_mkind } ->
        Estate(left_state_value_index (state self true y m_mkind) ei_list)

(* Make an assignment according to the sort of a variable [n] *)
let assign n { e_sort; e_size = ei_list } e =
  match e_sort with
  | In _ -> (* this case should not happend *) 
     Misc.internal_error "Translate: assign" Printer.name n
  | Out { y; tsort; self } ->
     match tsort with
     | Sort_val -> 
        (* this case should not happend *) 
        Misc.internal_error "Translate: assign (wrong sort)" Printer.name n
     | Sort_var -> Eassign(left_value_index (Eleft_name n) ei_list, e)
     | Sort_mem { m_mkind } ->
	Eassign_state(left_state_value_index
                        (state self false y m_mkind) ei_list, e)

(* Generate the code for a definition *)
(* [k] is the continuation. Either a local def [let id = e in k] or *)
(* an assignment, to a shared or state variable [self.id <- e; k] *)
let def n { e_typ; e_sort; e_size = ei_list } e k =
  match e_sort with
  | In _ -> (* this case should not happend *) 
     Misc.internal_error "Translate: def" Printer.name n
  | Out { y = id; tsort; self } ->
     match tsort with
     | Sort_val ->
        Elet(Evarpat { id; ty = Some(e_typ) }, e, k)
     | Sort_var ->
	Oaux.seq (Eassign(left_value_index (Eleft_name id) ei_list, e)) k
     | Sort_mem { m_mkind } ->
	Oaux.seq
	  (Eassign_state(left_state_value_index
			   (state self false id m_mkind) ei_list, e)) k
	  
(* Generate the code for [der x = e] *)
let der n { e_sort; e_size = ei_list } e k =
  match e_sort with
  | In _ -> 
     (* this case should not happend *) 
     Misc.internal_error "Translate: der" Printer.name n
  | Out { y; tsort; self } ->
     Oaux.seq
       (Eassign_state(left_state_value_index
			(Eleft_state_primitive_access
			   (Eleft_state_name { self; name = y }, Eder)) ei_list,
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
  let { e_typ; e_sort; e_size = ix_list } = entry_of n env in
  match e_sort with
  | In _ -> (* this case should not happend *)
     Misc.internal_error "Translate: out_of" Printer.name n
  | Out { y; tsort } -> y, e_typ, e_sort, ix_list

(* Translate the size type expression *)
let rec exp_of_sizetype si =
  let open Defsizes in
  match si with
  | Sint(i) -> Oaux.int_const i
  | Svar(n) -> Oaux.local n
  | Sfrac { num; denom } ->
     Oaux.div (exp_of_sizetype num) (Oaux.int_const denom)
  | Sop(op, s1, s2) ->
     let e1 = exp_of_sizetype s1 in
     let e2 = exp_of_sizetype s2 in
     match op with
     | Splus -> Oaux.plus e1 e2
     | Sminus -> Oaux.minus e1 e2
     | Smult -> Oaux.mult e1 e2

(* translate a size expression *)
let rec size env { Zelus.desc; Zelus.loc } =
  match desc with
  | Zelus.Size_int(i) -> Oaux.int_const i
  | Zelus.Size_var(n) -> var (entry_of n env)
  | Zelus.Size_frac { num; denom } ->
     Oaux.div (size env num) (Oaux.int_const denom)
  | Zelus.Size_op(op, s1, s2) ->
     let e1 = size env s1 in
     let e2 = size env s2 in
     match op with
     | Zelus.Size_plus -> Oaux.plus e1 e2
     | Zelus.Size_minus -> Oaux.minus e1 e2
     | Zelus.Size_mult -> Oaux.mult e1 e2

(* makes an initial value from a type. returns None when it fails *)
let choose ty =
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
let default ty v_opt =
  match v_opt with
  | None -> choose ty
  | Some(v) -> Some(Econst v)
			
(* Extension of an environment *)
(* The access to a state variable [x] is turned into the access on an *)
(* array access x.(i1)...(in) if loop_path = [i1;...;in] *)
let append loop_path l_env { self; env } =
  (* according to the sort of [id], it is represented as a state variable *)
  (* (an access of the form self.id), a shared variable (a reference), *)
  (* or a local variable (defined by a let/in) *)
  (* add a memory variable for every state variable in [l_env] *)
  (* and a [letvar] declaration for every shared variable *)
  let addrec n { t_sort; t_tys = { typ_body } } (env_acc, mem_acc, var_acc) =
    match t_sort with
    | Sort_val | Sort_mem { m_mkind = None; m_last = false;
                            m_init = No; m_shared = false } ->
       (* if [n] is a memory but no [last] nor [init] is defined *)
       (* it is treated as a local variable *)
       Env.add n
         { e_typ = typ_body; e_sort = Out { y = n; tsort = Sort_val; self };
           e_size = [] } env_acc,
       mem_acc, var_acc
      | Sort_var ->
	 Env.add n
           { e_typ = typ_body; e_sort = Out { y = n; tsort = Sort_var; self };
             e_size = [] } env_acc,
	 mem_acc,
         (n, is_mutable typ_body, typ_body, default typ_body None)
         :: var_acc
      | Sort_mem { m_mkind } ->
	 Env.add n
	   { e_typ = typ_body; e_sort = Out { y = n; tsort = t_sort; self };
             e_size = loop_path }
           env_acc,
	 Parseq.cons
           { m_name = n; m_value = choose typ_body; m_typ = typ_body;
	     m_kind = m_mkind; m_size = [] } mem_acc,
	 var_acc in
  let env_acc, mem_acc, var_acc =
    Env.fold addrec l_env (env, Parseq.empty, []) in
  { env = env_acc; self }, mem_acc, var_acc


(* Translation of a stateful function application [f se1 ... sen e] *)
(* if [loop_path = [i1;...;ik]
 * instance o = f se1 ... sen
 * call o.(i1)...(ik).step(e)
 * reset with o.(i1)...(ik).reset *)
let make_apply k loop_path code f arg_list =
  match k with
  | Deftypes.Tfun _ -> Eapp { f; arg_list }, code
  | Deftypes.Tnode _ ->
     (* the first [n-1] arguments are static *)
     let se_list, arg = Util.firsts arg_list in
     let f_opt = match f with | Eglobal { lname } -> Some lname | _ -> None in
     let loop_path =
       List.map (fun ix -> Oaux.local ix) loop_path in
     (* create an instance *)
     let o = Ident.fresh "i" in
     let j_code = { i_name = o; i_machine = f; i_kind = k;
		    i_params = se_list; i_size = [] } in
     let reset_code =
       Emethodcall({ met_machine = f_opt; met_name = Oaux.reset;
		     met_instance = Some(o, loop_path); met_args = [] }) in
     let step =
       Emethodcall({ met_machine = f_opt; met_name = Oaux.step;
		     met_instance = Some(o, loop_path); met_args = [arg] }) in
     step,
     { code with instances = Parseq.cons j_code code.instances;
                 reset = Oaux.seq reset_code code.reset }


(* Define a function or a machine according to a kind [k] *)
let make_machine
      f k pat_list self p { mem; instances; reset; assertions } e ty_res =
  { ma_name = f;
    ma_kind = k;
    ma_self = self;
    ma_params = pat_list;
    ma_initialize = None;
    ma_memories = Parseq.list [] mem;
    ma_instances = Parseq.list [] instances;
    ma_methods = 
      [ { me_name = Oaux.reset; me_params = []; me_body = reset;
          me_typ = Initial.typ_unit };
	{ me_name = Oaux.step; me_params = [p]; me_body = e;
          me_typ = ty_res } ];
    ma_assertion = Parseq.list [] assertions }

let exp_of_code f k pat_list self code e ty_res =
  let k = Interface.kindtype k in
  match k with
  | Deftypes.Tfun _ -> Efun { pat_list; e }
  | Deftypes.Tnode _ ->
    (* the [n-1] parameters are static *)
    let pat_list, p = Util.firsts pat_list in
    let body =
      make_machine f k pat_list self p code e ty_res in
    Emachine(body)

let add_mem_vars_to_code mem_acc var_acc (e, ({ mem } as code)) =
  letvar var_acc e, { code with mem = Parseq.seq mem_acc mem } 

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
     Evarpat { id; ty = Some(ty) }
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
     Econstr1pat(Lident.Modname(Initial.array_list_ident),
                 List.map pattern p_list)

(* Translation of a math/with handler. *)
let match_handlers body env loop_path code p_h_list =
  let body code { Zelus.m_pat; Zelus.m_body; Zelus.m_env } =
    let env, mem_acc, var_acc = append loop_path m_env env in
    let step, code = body env loop_path m_body code in
    { m_pat = pattern m_pat; m_body = letvar var_acc step },
    { code with mem = Parseq.seq mem_acc code.mem } in
  Util.mapfold body code p_h_list

let vardec { Zelus.var_name = id; Zelus.var_info = info } =
  let ty = Typinfo.get_type info in
  Evarpat { id; ty = Some(ty) }

let arg a_list =
  match a_list with | [] -> Ewildpat | _ -> Etuplepat (List.map vardec a_list)

(* Translation of expressions under an environment [env] *)
(* [context] is the context already generated *)
(* [expression env e context = e', context'] where [context'] extends *)
(* [context] with new *)
(* memory, instantiation and reset. *)
(* [loop_path = [i1;...;in]] is the loop path if [e] appears in *)
(* a nested loop forall in ... forall i1 do ... e ... *)
let rec expression env loop_path code { Zelus.e_desc } =
  match e_desc with
  | Zelus.Econst(i) -> Econst(immediate i), code
  | Zelus.Evar(n)
    | Zelus.Elast { id = n } ->
     var (entry_of n env), code
  | Zelus.Eglobal { lname = ln } ->
     Eglobal { lname = ln }, code
  | Zelus.Econstr0 { lname } ->
     Econstr0 { lname }, code
  | Zelus.Econstr1 { lname; arg_list } ->
     let arg_list, code =
       Util.mapfold (expression env loop_path) code arg_list in
     Econstr1 { lname; arg_list }, code
  | Zelus.Etuple(e_list) ->
     let e_list, context =
       Util.mapfold (expression env loop_path) code e_list in
     Etuple(e_list), context
  | Zelus.Erecord(label_e_list) ->
     let label_e_list, context =
       Util.mapfold
	 (fun context { Zelus.label; Zelus.arg } ->
           let arg, code = expression env loop_path code arg in
	   { label; arg }, context) code label_e_list in
     Erecord(label_e_list), context
  | Zelus.Erecord_access { Zelus.label; Zelus.arg } ->
     let arg, code =
       expression env loop_path code arg in
     Erecord_access { label; arg }, code
  | Zelus.Erecord_with(e_record, label_e_list) ->
     let e_record, code =
       expression env loop_path code e_record in
     let label_e_list, code =
       Util.mapfold
	 (fun code { Zelus.label; Zelus.arg } ->
           let arg, context = expression env loop_path code arg in
	   { label; arg }, context) code label_e_list in
     Erecord_with(e_record, label_e_list), code
  | Zelus.Etypeconstraint(e, ty_expression) ->
     let e, context = expression env loop_path code e in
     Etypeconstraint(e, ty_expression), context
  | Zelus.Eop(Zelus.Eup _, [e]) ->
     (* implement the zero-crossing up(x) by up(if x >=0 then 1 else -1) *)
     let e = if !Misc.zsign then Aux.sgn e else e in 
     expression env loop_path code e
  | Zelus.Eop(Zelus.Ehorizon _, [e]) ->
     expression env loop_path code e
  | Zelus.Eop(Zelus.Eifthenelse, [e1; e2; e3]) ->
     let e1, code = expression env loop_path code e1 in
     let e2, code = expression env loop_path code e2 in
     let e3, code = expression env loop_path code e3 in
     Eifthenelse(e1, e2, e3), code
  (* array operators *)
  | Zelus.Eop(Zelus.Earray(Earray_list), e_list) ->
     let e_list, code =
       Util.mapfold (expression env loop_path) code e_list in
     Earray_list e_list, code
  | Zelus.Eop(Zelus.Earray(Econcat), [e1; e2]) -> 
     let ty1 = Typinfo.get_type e1.e_info in
     let ty2 = Typinfo.get_type e2.e_info in
     let _, s1 = Types.filter_vec ty1 in
     let _, s2 = Types.filter_vec ty2 in
     let s1 = exp_of_sizetype s1 in
     let s2 = exp_of_sizetype s2 in
     let e1, code = expression env loop_path code e1 in
     let e2, code = expression env loop_path code e2 in
     Econcat { left = e1; left_size = s1; right = e2; right_size = s2 }, code
  | Zelus.Eop(Zelus.Earray(Eget), [e1; e2]) ->
     let e1, code = expression env loop_path code e1 in
     let e2, code = expression env loop_path code e2 in
     Eget { e = e1; index = e2 }, code
  | Zelus.Eop(Zelus.Earray(Eget_with_default), [e1; e2]) ->
     let e1, code = expression env loop_path code e1 in
     let e2, code = expression env loop_path code e2 in
     Eget { e = e1; index = e2 }, code
  | Zelus.Eop(Zelus.Earray(Eslice), [e1; e2; e]) ->
     let e1, code = expression env loop_path code e1 in
     let e2, code = expression env loop_path code e2 in
     let e, code = expression env loop_path code e in
     Eslice { e; left = e1; right = e2 }, code
  | Zelus.Eop(Zelus.Earray(Eupdate), [e1; i; e2]) ->
     let ty = Typinfo.get_type e1.e_info in
     let _, se = Types.filter_vec ty in
     let se = exp_of_sizetype se in
     let e1, code = expression env loop_path code e1 in
     let i, code = expression env loop_path code i in
     let e2, code = expression env loop_path code e2 in
     Eupdate { e = e1; index = i; arg = e2; size = se }, code
  | Zelus.Eop(Zelus.Earray(Etranspose), [e]) ->
     let ty = Typinfo.get_type e.e_info in
     let ty, s_1 = Types.filter_vec ty in
     let _, s_2 = Types.filter_vec ty in
     let size_1 = exp_of_sizetype s_1 in
     let size_2 = exp_of_sizetype s_2 in
     let e, code = expression env loop_path code e in
     Etranspose { e; size_1; size_2 }, code
  | Zelus.Eop(Zelus.Earray(Eflatten), [e]) ->
     let ty = Typinfo.get_type e.e_info in
     let ty, s_1 = Types.filter_vec ty in
     let _, s_2 = Types.filter_vec ty in
     let size_1 = exp_of_sizetype s_1 in
     let size_2 = exp_of_sizetype s_2 in
     let e, code = expression env loop_path code e in
     Eflatten { e; size_1; size_2 }, code
  | Zelus.Eop(Zelus.Earray(Ereverse), [e]) ->
     let ty = Typinfo.get_type e.e_info in
     let _, s = Types.filter_vec ty in
     let size = exp_of_sizetype s in
     let e, code = expression env loop_path code e in
     Ereverse { e; size }, code
  | Zelus.Eop(Zelus.Eatomic, [e]) ->
     expression env loop_path code e  
  | Zelus.Eop(Eseq, [e1; e2]) ->
     let e1, code  = expression env loop_path code e1 in
     let e2, code = expression env loop_path code e2 in
     Oaux.seq e1 e2, code
  | Zelus.Eapp { f; arg_list } ->
     (* make an application *)
     let make_app f arg_list =
       match arg_list with | [] -> f | _ -> Eapp { f; arg_list } in
     let ty = Typinfo.get_type f.e_info in
     (* compute the sequence of static arguments and non static ones *)
     let se_list, ne_list, ty_res = 
       Types.split_arguments ty arg_list in
     let f, code = expression env loop_path code f in
     let se_list, code =
       Util.mapfold (expression env loop_path) code se_list in
     let ne_list, code =
       Util.mapfold (expression env loop_path) code ne_list in
     let e_fun = make_app f se_list in
     let e_fun, code = match ne_list with
       | [] -> e_fun, code
       | _ -> let k = Types.kind_of_funtype ty_res in
	      make_apply k loop_path code e_fun ne_list in
     e_fun, code
  | Zelus.Esizeapp { f; size_list } ->
     (* for the moment only combinatorial size functions are treated *)
     let f, code = expression env loop_path code f in
     let size_list = List.map (size env) size_list in
     Esizeapp { f; size_list }, code
  | Zelus.Efun { Zelus.f_kind = k; Zelus.f_args = arg_list;
		 Zelus.f_body = r; Zelus.f_env = f_env; Zelus.f_hidden_env } ->
     let ty_res = Typinfo.get_type r.r_info in
     let pat_list = List.map arg arg_list in
     let f_env = Env.append f_hidden_env f_env in
     let self = Some(Ident.fresh "self") in
     let env, mem_acc, var_acc =
       append empty_loop_path f_env { self; env = env.env } in
     let e, code_body = result env r in
     let e, code_body =
       add_mem_vars_to_code mem_acc var_acc (e, code_body) in
     let f = Ident.fresh "machine" in
     exp_of_code f k pat_list self code_body e ty_res, code
  | Zelus.Ereset(e, r_e) ->
     let r_e, code = expression env loop_path code r_e in
     let e, ({ init } as code_e) =
       expression env loop_path empty_code e in
     (* execute the initialization code when [r_e] is true *)
     Oaux.seq (ifthen r_e init) e,
     seq code code_e    
  | Eforloop _ -> Misc.not_yet_implemented "for loops"
  | Zelus.Eassert(e) ->
     assertion_expression env loop_path code e
  | Zelus.Elet(l, e) ->
     leq_in_e env loop_path l code e
  | Zelus.Elocal(b, e) ->
     block_in_e env loop_path b code e
  | Zelus.Ematch { e; handlers } ->
     let e, code = expression env loop_path code e in
     let handlers, code =
       match_handlers
         (fun env loop_path e code -> expression env loop_path code e)
         env loop_path code handlers in
     Ematch(e, handlers), code
  | Zelus.Eop(Eperiod, _)  | Zelus.Eop _ | Zelus.Epresent _ ->
     (* these last constructions have been rewritten in previous steps *)
     assert false

and assertion_expression env loop_path code e =
  if !Misc.transparent then
    (* transparent assertions. [assert e] is translated as a machine *)
    (* whose input is [self] *)
    assertion env loop_path code e
  else
    let e, code = expression env loop_path code e in
    Eassert(e), code

(* transparent assertion. [e] is compiled as if it were a hybrid node *)
(* [hybrid self -> e] where [self] is the name of the closest memory state *)
(* surrending the assertion. The pre-condition to the translation is that *)
(* every free variable of the assertion is a state variable of the model. *)
and assertion { self; env } loop_path ({ assertions } as code) e =
  let self_pat =
    Evarpat { id = (match self with None -> assert false | Some(id) -> id);
              ty = None } in
    let self = Some(Ident.fresh "self") in
  let e, code_body =
    expression { self; env } empty_loop_path empty_code e in
  let f = Ident.fresh "machine" in
  let ma =
    make_machine f (Tnode(Tcont)) [] self self_pat code_body e Initial.typ_bool
  in
  Oaux.void, { code with assertions = Parseq.cons ma assertions }

and result env { Zelus.r_desc } =
  match r_desc with
  | Exp(e) -> expression env empty_loop_path empty_code e
  | Returns _ ->
     (* the returns handler has been eliminated in previous passes *)
     assert false

(* Translation of equations. They are traversed in reverse order *)
(* from the last one to the first one *)
(* [step,code] is the already generated code. The computations in *)
(* [code] are executed before [step] *)
and equation env loop_path { Zelus.eq_desc = desc } (step, code) =
  match desc with
  | Zelus.EQeq({ Zelus.pat_desc = Zelus.Evarpat(n) }, e) ->
     let e, code = expression env loop_path code e in
     def n (entry_of n env) e step, code
  | Zelus.EQeq(p, e) ->
     let e, code = expression env loop_path code e in
     letpat (pattern p) e step, code
  | Zelus.EQder { id; e; e_opt = None; handlers = [] } ->
     let e, code = expression env loop_path code e in
     der id (entry_of id env) e step, code
  | Zelus.EQder _ -> assert false
  | Zelus.EQmatch { e; handlers } ->
     let e, code = expression env loop_path code e in
     let handlers, code =
       match_handlers
         (fun env loop_path eq code ->
           equation env loop_path eq (Oaux.void, code))
         env loop_path code handlers in
     Oaux.seq (Ematch(e, handlers)) step, code
  | Zelus.EQreset({ Zelus.eq_desc = Zelus.EQinit(x, e) }, r_e)
       when not (Types.static e) ->
     let r_e, code = expression env loop_path code r_e in
     let e, ({ init } as e_code) = expression env loop_path empty_code e in
     Oaux.seq
       (ifthen r_e (Oaux.seq (assign x (entry_of x env) e) init)) step,
     seq code e_code
  | Zelus.EQreset(eq, r_e) ->
     let r_e, code = expression env loop_path code r_e in
     let e, ({ init } as code_eq) =
       equation env loop_path eq (Oaux.void, empty_code) in
     (* execute the initialization code when [r_e] is true *)
     Oaux.seq (ifthen r_e init) e, seq code code_eq
  | Zelus.EQinit(x, e) ->
     let e_c, code = expression env loop_path code e in
     let x_equal_e = assign x (entry_of x env) e_c in
     (* initialization of a state variable with a static value *)
     if Types.static e
     then step,
          seq { empty_code with init = x_equal_e; reset = x_equal_e } code
     else Oaux.seq x_equal_e step, code
  | Zelus.EQempty -> step, code
  | Zelus.EQand { ordered = true; eq_list } ->
     equation_list env loop_path eq_list (step, code)
  | Zelus.EQand _ -> assert false
  | Zelus.EQlocal(b) ->
     block env loop_path b (step, code)
  | Zelus.EQlet(l, eq_let) -> 
     leq_in_eq env loop_path l eq_let (step, code)
  | Zelus.EQif { e; eq_true; eq_false } ->
     let e, code = expression env loop_path code e in
     let e_true, code =
       equation env loop_path eq_true (Oaux.void, code) in
     let e_false, code =
       equation env loop_path eq_false (Oaux.void, code) in
     Oaux.seq (Oaux.ifthenelse e e_true e_false) step, code
  | Zelus.EQassert(e) ->
     assertion_equation env loop_path (step, code) e
  | Zelus.EQemit _ | Zelus.EQautomaton _ | Zelus.EQpresent _ -> assert false
  | Zelus.EQforloop _ -> Misc.not_yet_implemented "for loops"
  | Zelus.EQsizefun _ -> assert false
  
and assertion_equation env loop_path (step, code) e =
  if !Misc.transparent then
    (* transparent assertions *)
    step, code
  else
    let e, code = expression env loop_path code e in
    Oaux.seq (Eassert(e)) step, code

and sizefun_list env is_rec s_list (step, code) =
  let sizefun env { Zelus.sf_id; Zelus.sf_id_list; Zelus.sf_e; sf_env } =
    let env, _, _ = append empty_loop_path sf_env env in
     let sf_e, code = expression env empty_loop_path empty_code sf_e in
    { sf_id; sf_id_list; sf_e } in
  let s_list = List.map (sizefun env) s_list in
  Eletsizefun(is_rec, s_list, step), code

(* translate a list of equations [eq_list]; done from the last equation *)
(* to the first, that is *)
(* [equation_list [eq1;...;eqn] = equation eq1 (equation_list [eq2;...;eqn]) *)
and equation_list env loop_path eq_list (step, code) =
  List.fold_right
    (fun eq (step, code) ->
      equation env loop_path eq (step, code)) eq_list
    (step, code)

and leq_in_eq env loop_path
  { Zelus.l_rec; Zelus.l_eq; Zelus.l_env; Zelus.l_loc } eq_let (step, code) =
  let env, mem_acc, var_acc = append loop_path l_env env in
  let e, code = equation env loop_path eq_let (step, code) in
  let e, code =
    match Typing.eq_or_sizefun l_loc l_eq with
    | Left(eq_list) ->
    (* mutually recursive definition of streams *)
       equation_list env loop_path eq_list (e, code)
    | Right(s_list) ->
       (* mutually recursive definition of size functions *)
       sizefun_list env l_rec s_list (e, code) in
  add_mem_vars_to_code mem_acc var_acc (e, code)

and leq_in_e env loop_path
  { Zelus.l_rec; Zelus.l_eq; Zelus.l_env; Zelus.l_loc } code e =
  let env, mem_acc, var_acc = append loop_path l_env env in
  let e, code = expression env loop_path code e in
  let e, code =
    match Typing.eq_or_sizefun l_loc l_eq with
    | Left(eq_list) ->
    (* mutually recursive definition of streams *)
       equation_list env loop_path eq_list (e, code)
    | Right(s_list) ->
       (* mutually recursive definition of size functions *)
       sizefun_list env l_rec s_list (e, code) in
  add_mem_vars_to_code mem_acc var_acc (e, code)

and block env loop_path { Zelus.b_body; Zelus.b_env } (step, code) =
  let env, mem_acc, var_acc = append loop_path b_env env in
  let step, code = equation env loop_path b_body (step, code) in
  add_mem_vars_to_code mem_acc var_acc (step, code)

and block_in_e env loop_path { Zelus.b_body; Zelus.b_env } code e =
  let env, mem_acc, var_acc = append loop_path b_env env in
  let step, code = expression env loop_path code e in
  let step, code = equation env loop_path b_body (step, code) in
  add_mem_vars_to_code mem_acc var_acc (step, code)

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
     let e, _ = leq_in_e empty_env empty_loop_path d_leq empty_code ret in
     Eletdef [n_list, e]
	     
let program { Zelus.p_impl_list } =
  { p_impl_list = Util.iter implementation p_impl_list }
