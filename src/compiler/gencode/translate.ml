(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
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
			 
type code =
  { init: Obc.exp; (* sequence of initializations for [mem] *)
    mem: mentry Parseq.t; (* set of state variables *)
    instances: ientry Parseq.t; (* set of instances *)
    reset: Obc.exp; (* sequence of equations for resetting the block *)
    step: Obc.exp; (* body *)
  }

let fprint ff (env: entry Env.t) =
  let fprint_entry ff { e_typ = ty; e_sort = sort; e_size = size } =
    Format.fprintf ff "@[{ typ = %a;@,size = %a}@]"
		   Ptypes.output ty
		   (Pp_tools.print_list_r Printer.name "[" "," "]") size in
  Ident.Env.fprint_t fprint_entry ff env
		   
let empty_code = { mem = Parseq.empty; init = Oaux.void;
		   instances = Parseq.empty;
		   reset = Oaux.void; step = Oaux.void }

let seq { mem = m1; init = i1; instances = j1; reset = r1; step = s1 } 
	{ mem = m2; init = i2; instances = j2; reset = r2; step = s2 } =
  { mem = Parseq.seq m1 m2; init = Oaux.seq i1 i2; instances = Parseq.par j1 j2;
    reset = Oaux.seq r1 r2; step = Oaux.seq s1 s2 }

let empty_path = []

(** Look for an entry in the environment *)
let entry_of n env =
  try
    Env.find n env
  with Not_found ->
    Misc.internal_error "Unbound variable" Printer.name n

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
     | Deftypes.Encore | Deftypes.Major -> Eleft_state_name(n)

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
        Estate_access(left_state_value_index (state true n m_mkind) ei_list)

(* Make an assignment according to the sort of a variable [n] *)
let assign { e_sort; e_size = ei_list } e =
  match e_sort with
  | In _ -> assert false
  | Out(n, sort) ->
     match sort with
     | Sort_val -> assert false
     | Sort_var -> Eassign(left_value_index (Eleft_name n) ei_list, e)
     | Sort_mem { m_mkind } ->
	Eassign_state(left_state_value_index (state false n m_mkind) ei_list, e)

(* Generate the code for a definition *)
let def { e_typ; e_sort; e_size = ei_list } e ({ step = s } as code) =
  match e_sort with
  | In _ -> assert false
  | Out(id, sort) ->
     match sort with
     | Sort_val ->
        let step = Elet(Evarpat
                          { id; ty = Interface.type_expression_of_typ e_typ },
                        e, s) in
        { code with step }
                      
     | Sort_var ->
	{ code with step =
                      Oaux.seq
			(Eassign(left_value_index (Eleft_name id) ei_list, e))
			     s }
     | Sort_mem { m_mkind } ->
	let step = Oaux.seq
		     (Eassign_state(left_state_value_index
				      (state false id m_mkind) ei_list, e)) s in
        { code with step }
	  
(* Generate the code for [der x = e] *)
let der { e_sort; e_size = ei_list } e ({ step = s } as code) =
  match e_sort with
  | In _ -> assert false
  | Out(n, sort) ->
     let step =
       Oaux.seq (Eassign_state(left_state_value_index
				 (Eleft_state_primitive_access
				    (Eleft_state_name(n), Eder)) ei_list,
                               e)) s in
     { code with step }
       
(* Generate an if/then *)
let ifthen r_e i_code s = Oaux.seq (Eifthenelse(r_e, i_code, Oaux.void)) s
				   
(* Generate a for loop *)
let for_loop dir ix e1 e2 e_body =
  match e_body with
  | Econst (Evoid) | Esequence [] -> e_body
  | _ -> Efor { index = ix; dir = dir; left = e1; right = e2; e = e_body }

(* Generate the code for the definition of a value *)
let letpat p e ({ step = s } as code) =
  { code with step = Elet(p, e, s) }

(* Generate the code for initializing shared variables *)
let rec letvar l s =
  match l with
  | [] -> s
  | (id, is_mutable, ty, e_opt) :: l ->
     Eletvar { id; is_mutable; ty; e_opt; e = letvar l s }
				  
   
let out_of n env =
  let { e_typ = ty; e_sort = sort; e_size = ix_list } = entry_of n env in
  match sort with
  | In _ -> assert false
  | Out(x, sort) -> x, ty, sort, ix_list

(* Translate size expressions *)
let rec size_of_type si =
  let open Deftypes in
  match si with
  | Sint(i) -> Oaux.int_const i
  | Svar(n) -> Evar { is_mutable = false; id = n }
  | Sfrac { num; denom } ->
     Oaux.div (size_of_type num) (Oaux.int_const denom)
  | Sop(op, s1, s2) ->
     let e1 = size_of_type s1 in
     let e2 = size_of_type s2 in
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
  let ezero = Econst(Eint(42)) in
  let efzero = Econst(Efloat(42.0)) in
  let estring0 = Econst(Estring("aaaaaaa")) in
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
    | Tarrow _ -> eany
    | Tvec(ty, si) -> vec (value ty) (size_of_type si)
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

(** Computes a default value *)
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
      | Sort_val ->
	 Env.add n { e_typ = typ_body; e_sort = Out(n, t_sort); e_size = [] }
           env_acc,
	 mem_acc, var_acc
      | Sort_var ->
	 Env.add n { e_typ = typ_body; e_sort = Out(n, t_sort); e_size = [] }
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
  Env.fold addrec l_env (env, Parseq.empty, [])


(** Translation of a stateful function application [f se1 ... sen e] *)
(* if [loop_path = [i1;...;ik]
 * instance o = f se1 ... sen
 * call o.(i1)...(ik).step(e)
 * reset with o.(i1)...(ik).reset *)
let apply k env loop_path e e_list
	  ({ mem = m; init = i; instances = j; reset = r; step = s } as code) =
  match k with
  | Deftypes.Tfun _ -> Eapp { f = e; arg_list = e_list }, code
  | Deftypes.Tnode _ ->
     (* the first [n-1] arguments are static *)
     let se_list, arg = Util.firsts e_list in
     let f_opt = match e with | Eglobal { lname } -> Some lname | _ -> None in
     let loop_path =
       List.map (fun ix -> Evar { is_mutable = false; id = ix }) loop_path in
     (* create an instance *)
     let o = Ident.fresh "i" in
     let j_code = { i_name = o; i_machine = e; i_kind = k;
		    i_params = se_list; i_size = [] } in
     let reset_code =
       Emethodcall({ met_machine = f_opt; met_name = Oaux.reset;
		     met_instance = Some(o, loop_path); met_args = [] }) in
     let step_code =
       Emethodcall({ met_machine = f_opt; met_name = Oaux.step;
		     met_instance = Some(o, loop_path); met_args = [arg] }) in
     step_code,
     { code with instances = Parseq.cons j_code j;
		 init = Oaux.seq reset_code i;
		 reset = Oaux.seq reset_code r }
       
(** Translation of expressions under an environment [env] *)
(* [code] is the code already generated in the context. *)
(* [exp env e code = e', code'] where [code'] extends [code] with new *)
(* memory, instantiation and reset. The step field is untouched *)
(* [loop_path = [i1;...;in]] is the loop path if [e] appears in *)
(* a nested loop forall in ... forall i1 do ... e ... *)
let rec exp env loop_path code { Zelus.e_desc = desc } =
  match desc with
  | Zelus.Econst(i) -> Econst(immediate i), code
  | Zelus.Evar(n)
  | Zelus.Elast { id = n } -> var (entry_of n env), code
  | Zelus.Eglobal { lname = ln } -> Eglobal { lname = ln }, code
  | Zelus.Econstr0 { lname } -> Econstr0 { lname }, code
  | Zelus.Econstr1 { lname; arg_list } ->
      let arg_list, code = Util.mapfold (exp env loop_path) code arg_list in
      Econstr1 { lname; arg_list }, code
  | Zelus.Etuple(e_list) ->
     let e_list, code = Util.mapfold (exp env loop_path) code e_list in
     Etuple(e_list), code
  | Zelus.Erecord(label_e_list) ->
     let label_e_list, code =
       Util.mapfold
	 (fun code { Zelus.label; Zelus.arg } ->
           let arg, code = exp env loop_path code arg in
	   { label; arg }, code) code label_e_list in
     Erecord(label_e_list), code
  | Zelus.Erecord_access { Zelus.label; Zelus.arg } ->
     let arg, code =
       exp env loop_path code arg in
     Erecord_access { label; arg }, code
  | Zelus.Erecord_with(e_record, label_e_list) ->
     let e_record, code =
       exp env loop_path code e_record in
     let label_e_list, code =
       Util.mapfold
	 (fun code { Zelus.label; Zelus.arg } ->
           let arg, code = exp env loop_path code arg in
	   { label; arg }, code) code label_e_list in
     Erecord_with(e_record, label_e_list), code
  | Zelus.Etypeconstraint(e, ty_exp) ->
     let e, code = exp env loop_path code e in
     Etypeconstraint(e, ty_exp), code
  | Zelus.Eop(Zelus.Eup, [e]) ->
     (* implement the zero-crossing up(x) by up(if x >=0 then 1 else -1) *)
     let e = if !Misc.zsign then Aux.sgn e else e in 
     exp env loop_path code e
  | Zelus.Eop(Zelus.Ehorizon, [e]) ->
     exp env loop_path code e
  | Zelus.Eop(Zelus.Eifthenelse, [e1; e2; e3]) ->
     let e1, code = exp env loop_path code e1 in
     let e2, code = exp env loop_path code e2 in
     let e3, code = exp env loop_path code e3 in
     Eifthenelse(e1, e2, e3), code
  | Zelus.Eop(Zelus.Earray(Eget), [e1; e2]) ->
     let e1, code = exp env loop_path code e1 in
     let e2, code = exp env loop_path code e2 in
     Eget { e = e1; index = e2 }, code
  | Zelus.Eop(Zelus.Earray(Eupdate), [e1; i; e2]) ->
     let ty = Typinfo.get_type e1.e_info in
     let _, se = Types.filter_vec ty in
     let se = size_of_type se in
     let e1, code = exp env loop_path code e1 in
     let i, code = exp env loop_path code i in
     let e2, code = exp env loop_path code e2 in
     Eupdate { e = e1; index = i; arg = e2; size = se }, code
  | Zelus.Eop(Zelus.Earray(Eslice), [e1; e2; e]) ->
     let e1, code = exp env loop_path code e1 in
     let e2, code = exp env loop_path code e2 in
     let e, code = exp env loop_path code e in
     Eslice { e; left = e1; right = e2 }, code
  | Zelus.Eop(Zelus.Earray(Econcat), [e1; e2]) -> 
     let ty1 = Typinfo.get_type e1.e_info in
     let ty2 = Typinfo.get_type e2.e_info in
     let _, s1 = Types.filter_vec ty1 in
     let _, s2 = Types.filter_vec ty2 in
     let s1 = size_of_type s1 in
     let s2 = size_of_type s2 in
     let e1, code = exp env loop_path code e1 in
     let e2, code = exp env loop_path code e2 in
     Econcat { left = e1; left_size = s1; right = e2; right_size = s2 }, code
  | Zelus.Eop(Zelus.Eatomic, [e]) ->
     exp env loop_path code e  
  | Zelus.Elet _ | Zelus.Eop(Eseq, _) | Zelus.Eop(Eperiod, _) 
  | Zelus.Eop _ | Zelus.Epresent _
  | Zelus.Ematch _ | Zelus.Elocal _ -> assert false
  | Zelus.Eapp { f; arg_list } ->
     (* make an application *)
     let make_app f arg_list =
       match arg_list with | [] -> f | _ -> Eapp { f; arg_list } in
     let ty = Typinfo.get_type f.e_info in
     (* compute the sequence of static arguments and non static ones *)
     let se_list, ne_list, ty_res = 
       Types.split_arguments ty arg_list in
     let f, code = exp env loop_path code f in
     let se_list, code = Util.mapfold (exp env loop_path) code se_list in
     let ne_list, code = Util.mapfold (exp env loop_path) code ne_list in
     let e_fun = make_app f se_list in
     match ne_list with
     | [] -> e_fun, code
     | _ -> let k = Types.kind_of_funtype ty_res in
	    apply k env loop_path e_fun ne_list code
  			 
(** Patterns *)
and pattern { Zelus.pat_desc = desc; Zelus.pat_info = info } =
  let ty = Typinfo.get_type info in
  match desc with
  | Zelus.Ewildpat -> Ewildpat
  | Zelus.Econstpat(im) -> Econstpat(immediate im)
  | Zelus.Econstr0pat(c0) -> Econstr0pat(c0)
  | Zelus.Econstr1pat(c1, p_list) ->
      Econstr1pat(c1, List.map pattern p_list)
  | Zelus.Etuplepat(p_list) -> Etuplepat(List.map pattern p_list)
  | Zelus.Evarpat(id) -> Evarpat { id; ty = Interface.type_expression_of_typ ty }
  | Zelus.Erecordpat(label_pat_list) ->
     Erecordpat
       (List.map
          (fun { Zelus.label; Zelus.arg } -> { label; arg = pattern arg })
	  label_pat_list)
  | Zelus.Etypeconstraintpat(p, ty) ->
     Etypeconstraintpat(pattern p, ty)
  | Zelus.Ealiaspat(p, n) -> Ealiaspat(pattern p, n)
  | Zelus.Eorpat(p1, p2) -> Eorpat(pattern p1, pattern p2)
				  
(** Equations *)
let rec equation env loop_path { Zelus.eq_desc = desc } code =
  match desc with
  | Zelus.EQeq({ Zelus.pat_desc = Zelus.Evarpat(n) }, e) ->
     let e, code = exp env loop_path code e in
     def (entry_of n env) e code
  | Zelus.EQeq(p, e) ->
     let e, code = exp env loop_path code e in
     letpat (pattern p) e code
  | Zelus.EQder { id; e; e_opt = None; handlers = [] } ->
     let e, code = exp env loop_path code e in
     der (entry_of id env) e code
  | Zelus.EQmatch { e; handlers } ->
     let e, code = exp env loop_path code e in
     let handlers, p_h_code = match_handlers env loop_path handlers in
     seq { p_h_code with step = Ematch(e, handlers) } code
  | Zelus.EQreset({ Zelus.eq_desc = Zelus.EQinit(x, e) }, r_e)
       when not (Types.static e) ->
     let r_e, code = exp env loop_path code r_e in
     let e, ({ init = i_code } as e_code) = exp env loop_path empty_code e in
     let { step = s } as code = seq e_code code in
     { code with step =
                   ifthen r_e (Oaux.seq (assign (entry_of x env) e) i_code) s }
  | Zelus.EQreset(eq, r_e) ->
      let { init = i_code } = code in
      let { init = ri_code } as r_code =
        equation env loop_path eq { code with init = Esequence [] } in
      let r_e, r_code = exp env loop_path r_code r_e in
      (* execute the initialization code when [e] is true *)
     let { step = s } as code = seq r_code { empty_code with init = i_code } in
     { code with step = ifthen r_e ri_code s }
  | Zelus.EQinit(x, e) ->
     let e_c, code = exp env loop_path code e in
     let x_e = assign (entry_of x env) e_c in
     (* initialization of a state variable with a static value *)
     if Types.static e
     then seq { empty_code with init = x_e; reset = x_e } code
     else seq { empty_code with step = x_e } code
  | Zelus.EQempty -> code
  | Zelus.EQand { ordered = true; eq_list } ->
     equation_list env loop_path eq_list code
  | Zelus.EQif _ -> Misc.not_yet_implemented "if"
  | Zelus.EQassert _ -> Misc.not_yet_implemented "assert"
  | Zelus.EQforloop _ -> Misc.not_yet_implemented "for loops"
  | Zelus.EQlet _ -> Misc.not_yet_implemented "let"
  | Zelus.EQsizefun _ -> Misc.not_yet_implemented "sizefun"
  | Zelus.EQand _ | Zelus.EQlocal _
  | Zelus.EQder _ | Zelus.EQemit _ | Zelus.EQautomaton _ 
  | Zelus.EQpresent _ -> assert false
				
and equation_list env loop_path eq_list code =
  List.fold_right (fun eq code -> equation env loop_path eq code) eq_list code
		  
(* Translation of a math/with handler. *)
and match_handlers env loop_path p_h_list =
  let body code { Zelus.m_pat = p; Zelus.m_body = b; Zelus.m_env = m_env } =
    let env, mem_acc, var_acc = append loop_path m_env env in
    let { mem = m_code; step = s_code } as b_code =  block env loop_path b in
    { m_pat = pattern p; m_body = letvar var_acc s_code },
    seq code
	{ b_code with step = Esequence []; mem = Parseq.seq mem_acc m_code } in
  Util.mapfold body empty_code p_h_list
	  
and local env loop_path { Zelus.l_eq = eq; Zelus.l_env = l_env } e =
  let env, mem_acc, var_acc = append loop_path l_env env in
  let e, code = exp env loop_path empty_code e in
  let eq_code =
    equation env loop_path eq { code with step = Oexp(e) } in
  add_mem_vars_to_code eq_code mem_acc var_acc
    
and block env loop_path { Zelus.b_body = eq; Zelus.b_env = b_env  } =
  let env, mem_acc, var_acc = append loop_path b_env env in
  let eq_code = equation env loop_path eq empty_code in
  add_mem_vars_to_code eq_code mem_acc var_acc

and add_mem_vars_to_code ({ mem; step } as code) mem_acc var_acc =
  { code with mem = Parseq.seq mem_acc mem; step = letvar var_acc step }
         
(* Define a function or a machine according to a kind [k] *)
let machine n k pat_list { mem = m; instances = j; reset = r; step = s }
	    ty_res =
  let k = Interface.kindtype k in
  match k with
  | Deftypes.Tfun _ -> Eletfun(n, pat_list, s)
  | Deftypes.Tnode _ ->
    (* the [n-1] parameters are static *)
    let pat_list, p = Util.firsts pat_list in
    let body =
       { ma_kind = k;
	 ma_params = pat_list;
	 ma_initialize = None;
	 ma_memories = Parseq.list [] m;
	 ma_instances = Parseq.list [] j;
	 ma_methods = 
	   [ { me_name = Oaux.reset; me_params = []; me_body = r;
               me_typ = Initial.typ_unit };
	     { me_name = Oaux.step; me_params = [p]; me_body = s;
               me_typ = ty_res } ] } in
     Eletmachine(n, body)
 
(* Translation of an expression. After normalisation *)
(* the body of a function is either of the form [e] with [e] stateless *)
(* or [let Eq in e] with [e] stateless *)
let expression env ({ Zelus.e_desc = desc } as e) =
  match desc with
  | Zelus.Elet(l, e_let) -> local env empty_path l e_let
  | _ -> let e, code = exp env empty_path empty_code e in
	 { code with step = Oexp(e) }       
 
(** Translation of a declaration *)
let implementation { Zelus.desc = desc } =
  match desc with
  | Zelus.Eopen(n) -> Eopen(n)
  | Zelus.Etypedecl(n, params, ty_decl) ->
     Etypedecl([n, params, type_of_type_decl ty_decl])
  | Zelus.Econstdecl(n, _, e) ->
     (* There should be no memory allocated by [e] *)
     let { step = s } = expression Env.empty e in
     Eletvalue(n, s)
  | Zelus.Efundecl(n, { Zelus.f_kind = k; Zelus.f_args = pat_list;
			Zelus.f_body = e; Zelus.f_env = f_env }) ->
     let pat_list = List.map pattern pat_list in
     let env, mem_acc, var_acc = append empty_path f_env Env.empty in
     let code = expression env e in
     let code = add_mem_vars_to_code code mem_acc var_acc in
     machine n k pat_list code e.Zelus.e_typ
	     
let implementation_list impl_list = Util.iter implementation impl_list
