(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2016                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* translation from zelus code to obc *)
(* applied to normalized and scheduled code *)
open Misc
open Ident
open Global
open Deftypes
open Obc
       
(* Basic constants *)
let one = Oconst(Oint(1))
		 
(* addition, subtraction *)
let plus e1 e2 =
  Oapp(Oglobal(Lident.Modname(Initial.pervasives_name "+")),[e1; e2])
let minus e1 e2 =
  Oapp(Oglobal(Lident.Modname(Initial.pervasives_name "-")),[e1; e2])

(* application *)
let app e_fun e_list =
  match e_list with | [] -> e_fun | _ -> Oapp(e_fun, e_list)
					     
let sequence inst1 inst2 =
  match inst1, inst2 with
  | (Osequence [], inst) | (inst, Osequence []) -> inst
  | Osequence(l1), Osequence(l2) -> Osequence(l1 @ l2)
  | _, Osequence(l2) -> Osequence(inst1 :: l2)
  | _ -> Osequence [inst1; inst2]

(** Translating type expressions. *)
let rec type_expression { Zelus.desc = desc } =
  match desc with
  | Zelus.Etypevar(s) -> Otypevar(s)
  | Zelus.Etypeconstr(ln, ty_list) ->
     Otypeconstr(ln, List.map type_expression ty_list)
  | Zelus.Etypetuple(ty_list) ->
    Otypetuple(List.map type_expression ty_list)
  | Zelus.Etypevec(ty, s) ->
     Otypevec(type_expression ty, size s)
  | Zelus.Etypefun(_, _, opt_name, ty_arg, ty_res) ->
     Otypefun(opt_name, type_expression ty_arg, type_expression ty_res)

and type_of_type_decl ty_decl =
  match ty_decl with
  | Zelus.Eabstract_type -> Oabstract_type
  | Zelus.Eabbrev(ty) -> Oabbrev(type_expression ty)
  | Zelus.Evariant_type(n_list) ->
     Ovariant_type(List.map (fun n -> Oconstr0decl(n)) n_list)
  | Zelus.Erecord_type(n_ty_list) ->
     Orecord_type(List.map (fun (n, ty) -> (n, type_expression ty)) n_ty_list)

and size { Zelus.desc = desc } =
  match desc with
  | Zelus.Sconst(i) -> Sconst(i)
  | Zelus.Sglobal(ln) ->  Sglobal(ln)
  | Zelus.Sname(n) -> Sname(n)
  | Zelus.Sop(op, s1, s2) ->
     let operator = function Zelus.Splus -> Splus | Zelus.Sminus -> Sminus in
     Sop(operator op, size s1, size s2)

		 
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
			 
type 'a code =
    { mem: mentry State.t; (* set of state variables *)
      init: Obc.inst; (* sequence of initializations for [mem] *)
      instances: ientry State.t; (* set of instances *)
      reset: Obc.inst; (* sequence of equations for resetting the block *)
      step: 'a; (* body *)
      }

let empty_code = { mem = State.empty; init = Osequence [];
		   instances = State.empty;
		   reset = Osequence []; step = Osequence [] }

let seq { mem = m1; init = i1; instances = j1; reset = r1; step = s1 } 
	{ mem = m2; init = i2; instances = j2; reset = r2; step = s2 } =
  { mem = State.seq m1 m2; init = sequence i1 i2; instances = State.par j1 j2;
    reset = sequence r1 r2; step = sequence s1 s2 }

let empty_path = []

(** Look for an entry in the environment *)
let entry_of n env =
  try Env.find n env with Not_found ->
    Misc.internal_error "Unbound variable" Printer.name n


(** Translation of immediate values *)
let immediate = function
  | Deftypes.Eint(i) -> Oint(i)
  | Deftypes.Efloat(f) -> Ofloat(f)
  | Deftypes.Ebool(b) -> Obool(b)
  | Deftypes.Echar(c) -> Ochar(c)
  | Deftypes.Estring(s) -> Ostring(s)
  | Deftypes.Evoid -> Ovoid

let constant = function
  | Deftypes.Cimmediate(i) -> Oconst(immediate i)
  | Deftypes.Cglobal(ln) -> Oglobal(ln)

(* read/write of a state variable. *)
let state is_read n k =
  match k with
  | None -> Oleft_state_name(n)
  | Some(k) ->
     match k with
     | Deftypes.Cont ->
	Oleft_state_primitive_access (Oleft_state_name(n), Ocont)
     | Deftypes.Zero ->
	Oleft_state_primitive_access
	  (Oleft_state_name(n), if is_read then Ozero_in else Ozero_out)
     | Deftypes.Horizon | Deftypes.Period | Deftypes.Encore ->
					     Oleft_state_name(n)

(* index in an array *)
let rec index e =
  function [] -> e | ei :: ei_list -> Oindex(index e ei_list, Olocal(ei))

let rec left_value_index lv =
  function
  | [] -> lv
  | ei :: ei_list -> Oleft_index(left_value_index lv ei_list, Olocal(ei))

let rec left_state_value_index lv = function
  | [] -> lv
  | ei :: ei_list ->
     Oleft_state_index(left_state_value_index lv ei_list, Olocal(ei))
						      
(* read of a variable *)
let var { e_sort = sort; e_size = ei_list } =
  let e = match sort with
    | In(e) -> e
    | Out(n, sort) ->
       match sort with
       | Sstatic | Sval -> Olocal(n)
       | Svar _ -> Ovar(n)
       | Smem { m_kind = k } -> Ostate(state true n k) in
  index e ei_list

(** Make an assignment according to the sort of a variable [n] *)
let assign { e_sort = sort; e_size = ei_list } e =
  match sort with
  | In _ -> assert false
  | Out(n, sort) ->
     match sort with
     | Sstatic | Sval -> assert false
     | Svar _ -> Oassign(left_value_index (Oleft_name n) ei_list, e)
     | Smem { m_kind = k } ->
	Oassign_state(left_state_value_index (state false n k) ei_list, e)

(** Generate the code for a definition *)
let def { e_typ = ty; e_sort = sort; e_size = ei_list } e ({ step = s } as code) =
  match sort with
  | In _ -> assert false
  | Out(n, sort) ->
     match sort with
     | Sstatic | Sval -> { code with step = Olet(Ovarpat(n, ty), e, s) }
     | Svar _ ->
	{ code with step = sequence
			     (Oassign(left_value_index (Oleft_name n) ei_list, e))
			     s }
     | Smem { m_kind = k } ->
	{ code with step = sequence
			     (Oassign_state(left_state_value_index
					      (state false n k) ei_list, e)) s }
	  
(** Generate the code for [der x = e] *)
let der { e_sort = sort; e_size = ei_list } e ({ step = s } as code) =
  match sort with
  | In _ -> assert false
  | Out(n, sort) ->
     { code with step =
		   sequence
		     (Oassign_state(left_state_value_index
				      (Oleft_state_primitive_access
					 (Oleft_state_name(n), Oder)) ei_list, e))
		     s }
       
(** Generate an if/then *)
let ifthen r_e i_code s = sequence (Oif(r_e, i_code)) s
				   
(** Generate a for loop *)
let for_loop direction ix e1 e2 i_body =
  match i_body with
  | Osequence [] -> Osequence []
  | _ -> Ofor(direction, ix, e1, e2, i_body)

(** Generate the code for the definition of a value *)
let letpat p e ({ step = s } as code) =
  { code with step = Olet(p, e, s) }

(** Generate the code for initializing shared variables *)
let rec letvar l s =
  match l with
  | [] -> s
  | (n, ty, v_opt) :: l -> Oletvar(n, ty, v_opt, letvar l s)
				  
(** Compile an equation [n += e] *)
let pluseq ({ e_sort = sort; e_size = ei_list } as entry)
	   e ({ step = s } as code) =
  let ln =
    match sort with
    | In _ -> assert false
    | Out(n, sort) ->
       match sort with
       | Svar { v_combine = Some(ln) } | Smem { m_combine = Some(ln) } -> ln
       | _ -> Misc.internal_error "Unbound variable" Printer.name n in
  { code with step =
		sequence (assign entry
				 (Oapp(Oglobal(ln), [var entry; e]))) s }
    
let out_of n env =
  let { e_typ = ty; e_sort = sort; e_size = ix_list } = entry_of n env in
  match sort with
  | In _ -> assert false
  | Out(x, sort) -> x, ty, sort, ix_list

(** Translate size expressions *)
let rec size env = function
  | Tconst(i) -> Oconst(Oint(i))
  | Tglobal(qualident) -> Oglobal(Lident.Modname(qualident))
  | Tname n -> var (entry_of n env)
  | Top(op, s1, s2) ->
     let e1 = size env s1 in
     let e2 = size env s2 in
     match op with
     | Tplus -> plus e1 e2
     | Tminus -> minus e1 e2
  
(* makes an initial value from a type. returns None when it fails *)
let choose env ty =
  let tuple l = Otuple(l) in
  let efalse = Oconst(Obool(false)) in
  let echar0 = Oconst(Ochar('a')) in
  let ezero = Oconst(Oint(0)) in
  let efzero = Oconst(Ofloat(0.0)) in
  let estring0 = Oconst(Ostring("")) in
  let evoid = Oconst(Ovoid) in
  let eany = Oconst(Oany) in
  let vec e s = Ovec(e, s) in
  let rec value_from_deftype id =
    try
      let { info = { type_desc = ty_c } } = 
        Modules.find_type (Lident.Modname(id)) in
      match ty_c with
        | Variant_type({ qualid = qualid } :: _) ->
            Oconstr0(Lident.Modname(qualid))
        | Abstract_type | Variant_type _ -> eany
        | Record_type(l_list) ->
           Orecord(
	       List.map 
                 (fun { qualid = qualid; info = { label_res = ty } } -> 
                  (Lident.Modname(qualid), value ty)) l_list)
        | Abbrev(_, ty) -> value ty
    with
      | Not_found -> eany
  and value ty =
    match ty.t_desc with
    | Tvar -> eany
    | Tproduct(ty_l) -> tuple (List.map value ty_l)
    | Tfun _ -> eany
    | Tvec(ty, s) -> vec (value ty) (size env s)
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
    | Tlink(link) -> value link in
  Some(value ty)

(** Computes a default value *)
let default env ty v_opt =
  match v_opt with
  | None -> choose env ty
  | Some(v) -> Some(constant v)
			
(** Extension of an environment *)
(* The access to a state variable [x] is turned into the access on an *)
(* array access x.(i1)...(in) if loop_path = [i1;...;in] *)
let append loop_path l_env env =
  (* add a memory variable for every state variable in [l_env] *)
  (* and a [letvar] declaration for every shared variable *)
  let addrec n { t_sort = k; t_typ = ty } (env_acc, mem_acc, var_acc) =
    match k with
      | Sstatic
      | Sval ->
	 Env.add n { e_typ = ty; e_sort = Out(n, k); e_size = [] } env_acc,
	 mem_acc, var_acc
      | Svar { v_default = v_opt } ->
	 Env.add n { e_typ = ty; e_sort = Out(n, k); e_size = [] } env_acc,
	 mem_acc, (n, ty, default env ty v_opt) :: var_acc
      | Smem { m_kind = k_opt } ->
	 Env.add n
		 { e_typ = ty; e_sort = Out(n, k); e_size = loop_path } env_acc,
	 State.cons { m_name = n; m_value = choose env ty; m_typ = ty;
		      m_kind = k_opt; m_size = [] } mem_acc,
	 var_acc in
  Env.fold addrec l_env (env, State.empty, [])


(** Translation of a stateful function application [f se1 ... sen e] *)
(* if [loop_path = [i1;...;ik]
 * instance o = f se1 ... sen
 * call o.(i1)...(ik).step(e)
 * reset with o.(i1)...(ik).reset *)
let apply k env loop_path e e_list
	  ({ mem = m; init = i; instances = j; reset = r; step = s } as code) =
  match k with
  | Deftypes.Tstatic _
  | Deftypes.Tany | Deftypes.Tdiscrete(false) -> Oapp(e, e_list), code
  | Deftypes.Tdiscrete(true)
  | Deftypes.Tcont ->
     (* the first [n-1] arguments are static *)
     let se_list, arg = Misc.firsts e_list in
     let f_opt = match e with | Oglobal(g) -> Some(g) | _ -> None in
     let loop_path = List.map (fun ix -> Olocal(ix)) loop_path in
     (* create an instance *)
     let o = Ident.fresh "i" in
     let j_code = { i_name = o; i_machine = e; i_kind = k;
		    i_params = se_list; i_size = [] } in
     let reset_code =
       Omethodcall({ met_machine = f_opt; met_name = Oreset;
		     met_instance = Some(o, loop_path); met_args = [] }) in
     let step_code =
       Omethodcall({ met_machine = f_opt; met_name = Ostep;
		     met_instance = Some(o, loop_path); met_args = [arg] }) in
     step_code,
     { code with instances = State.cons j_code j;
		 init = sequence (Oexp(reset_code)) i;
		 reset = sequence (Oexp(reset_code)) r }
       
(** Translation of expressions under an environment [env] *)
(* [code] is the code already generated in the context. *)
(* [exp env e code = code'] where [code'] extends [code] with new *)
(* memory, instantiation and reset. The step field is untouched *)
(* [loop_path = [i1;...;in]] is the loop path if [e] appears in *)
(* a nested loop forall in ... forall i1 do ... e ... *)
let rec exp env loop_path code { Zelus.e_desc = desc } =
  match desc with
  | Zelus.Econst(i) -> Oconst(immediate i), code
  | Zelus.Elocal(n)
  | Zelus.Elast(n) -> var (entry_of n env), code
  | Zelus.Eglobal { lname = ln } -> Oglobal(ln), code
  | Zelus.Econstr0(ln) -> Oconstr0(ln), code
  | Zelus.Etuple(e_list) ->
     let e_list, code = Misc.map_fold (exp env loop_path) code e_list in
     Otuple(e_list), code
  | Zelus.Erecord(label_e_list) ->
     let label_e_list, code =
       Misc.map_fold
	 (fun code (l, e) -> let e, code = exp env loop_path code e in
			     (l, e), code) code label_e_list in
     Orecord(label_e_list), code
  | Zelus.Erecord_access(e, longname) ->
     let e, code = exp env loop_path code e in Orecord_access(e, longname), code
  | Zelus.Etypeconstraint(e, ty) ->
     let e, code = exp env loop_path code e in
     Otypeconstraint(e, type_expression ty), code
  | Zelus.Eop((Zelus.Eup | Zelus.Ehorizon), [e]) ->
     exp env loop_path code e
  | Zelus.Eop(Zelus.Eafter _, [e]) -> exp env loop_path code e
  | Zelus.Eop(Zelus.Eifthenelse, [e1; e2; e3]) ->
     let e1, code = exp env loop_path code e1 in
     let e2, code = exp env loop_path code e2 in
     let e3, code = exp env loop_path code e3 in
     Oifthenelse(e1, e2, e3), code
  | Zelus.Eop(Zelus.Eaccess, [e1; e2]) ->
     let e1, code = exp env loop_path code e1 in
     let e2, code = exp env loop_path code e2 in
     Oindex(e1, e2), code
  | Zelus.Elet _ | Zelus.Eseq _ | Zelus.Eperiod _ 
  | Zelus.Eop _ | Zelus.Epresent _ | Zelus.Ematch _ | Zelus.Eblock _ ->
						       assert false
  | Zelus.Eapp(_, e_fun, e_list) ->
     (* compute the sequence of static arguments and non static ones *)
     let se_list, ne_list, ty_res =
       Types.split_arguments e_fun.Zelus.e_typ e_list in
     let e_fun, code = exp env loop_path code e_fun in
     let se_list, code = Misc.map_fold (exp env loop_path) code se_list in
     let ne_list, code = Misc.map_fold (exp env loop_path) code ne_list in
     let e_fun = app e_fun se_list in
     match ne_list with
     | [] -> e_fun, code
     | _ -> let k = Types.kind_of_funtype ty_res in
	    apply k env loop_path e_fun ne_list code
  			 
(** Patterns *)
and pattern { Zelus.p_desc = desc; Zelus.p_typ = ty } =
  match desc with
  | Zelus.Ewildpat -> Owildpat
  | Zelus.Econstpat(im) -> Oconstpat(immediate im)
  | Zelus.Econstr0pat(c0) -> Oconstr0pat(c0)
  | Zelus.Etuplepat(p_list) -> Otuplepat(List.map pattern p_list)
  | Zelus.Evarpat(n) -> Ovarpat(n, ty)
  | Zelus.Erecordpat(label_pat_list) ->
     Orecordpat(List.map (fun (label, pat) -> (label, pattern pat))
			 label_pat_list)
  | Zelus.Etypeconstraintpat(p, ty) ->
     Otypeconstraintpat(pattern p, type_expression ty)
  | Zelus.Ealiaspat(p, n) -> Oaliaspat(pattern p, n)
  | Zelus.Eorpat(p1, p2) -> Oorpat(pattern p1, pattern p2)
				  
(** Equations *)
let rec equation env loop_path { Zelus.eq_desc = desc } code =
  match desc with
  | Zelus.EQeq({ Zelus.p_desc = Zelus.Evarpat(n) }, e) ->
     let e, code = exp env loop_path code e in
     def (entry_of n env) e code
  | Zelus.EQeq(p, e) ->
     let e, code = exp env loop_path code e in
     letpat (pattern p) e code
  | Zelus.EQpluseq(n, e) ->
     let e, code = exp env loop_path code e in
     pluseq (entry_of n env) e code
  | Zelus.EQder(n, e, None, []) ->
     let e, code = exp env loop_path code e in
     der (entry_of n env) e code
  | Zelus.EQmatch(_, e, p_h_list) ->
     let e, code = exp env loop_path code e in
     let p_step_h_list, p_h_code = match_handlers env loop_path p_h_list in
     seq { p_h_code with step = Omatch(e, p_step_h_list) } code
  | Zelus.EQreset([{ Zelus.eq_desc = Zelus.EQinit(x, e) }], r_e)
       when not (Reset.static e) ->
     let r_e, code = exp env loop_path code r_e in
     let e, ({ init = i_code } as e_code) = exp env loop_path empty_code e in
     let { step = s } as code = seq e_code code in
     { code with step = ifthen r_e (sequence (assign (entry_of x env) e) i_code) s }
  | Zelus.EQreset(eq_list, r_e) ->
     let r_e, code = exp env loop_path code r_e in
     let { init = i_code } as r_code =
       equation_list env loop_path eq_list empty_code in
     (* execute the initialization code when [e] is true *)
     let { step = s } as code = seq r_code code in
     { code with step = ifthen r_e i_code s }
  | Zelus.EQinit(x, e) ->
     let e_c, code = exp env loop_path code e in
     let x_e = assign (entry_of x env) e_c in
     (* initialization of a state variable with a static value *)
     if Reset.static e
     then seq { empty_code with init = x_e; reset = x_e } code
     else seq { empty_code with step = x_e } code
  | Zelus.EQforall { Zelus.for_index = i_list; Zelus.for_init = init_list;
		     Zelus.for_body = b_eq_list } ->
     (* [forall i in e1..e2, xi in ei,..., oi in o,... do body done]
      * is translated into:
      * for i = e1 to e2 do
          ...
      * with xi into ei.(i), oi into o.(i)
      * - every instance o from the body must be an array
      * - every state variable m from the body must be an array *)
     (* look for the index [i in e1..e2] *)
     let rec index code = function
       | [] -> let id = Ident.fresh "i" in
	       (id, Oconst(Oint(0)), Oconst(Oint(0))), code
       | { Zelus.desc = desc } :: i_list ->
	  match desc with
	  | Zelus.Eindex(x, e1, e2) ->
	     let e1, code = exp env loop_path code e1 in
	     let e2, code = exp env loop_path code e2 in
	     (x, e1, e2), code
	  | Zelus.Einput _ | Zelus.Eoutput _ -> index code i_list in
     (* extend the environment for in/out variables *)
     (* [ix] is the index of the loop *)
     let in_out ix (env_acc, code) { Zelus.desc = desc } =
       match desc with
       | Zelus.Einput(x, ({ Zelus.e_typ = ty } as e)) ->
	  let e, code = exp env loop_path code e in
	  Env.add x { e_typ = ty; e_sort = In(e); e_size = [ix] } env_acc, code
       | Zelus.Eoutput(x, y) ->
	  let y, ty, sort, ix_list = out_of y env in
	  Env.add x { e_typ = ty; e_sort = Out(y, sort);
		      e_size = ix :: ix_list } env_acc, code
       | Zelus.Eindex(i, { Zelus.e_typ = ty }, _) ->
	  Env.add i { e_typ = ty; e_sort = Out(i, Deftypes.Sval);
		      e_size = [] } env_acc, code in
     (* transforms an instance into an array of instances *)
     let array_of_instance size ({ i_size } as ientry) =
       { ientry with i_size = size :: i_size } in
     let array_of_memory size ({ m_size } as mentry) =
       { mentry with m_size = size :: m_size } in
     (* generate the code for the initialization part of the for loop *)
     let init code { Zelus.desc = desc } =
       match desc with
       | Zelus.Einit_last(x, e) ->
	  let e, code = exp env loop_path code e in
	  assign (entry_of x env) e, code
       | Zelus.Einit_value(x, e, _) ->
	  let e, code = exp env loop_path code e in
	  assign (entry_of x env) e, code in
     (* first compute the index [i in e1 .. e2] *)
     let (ix, e1, e2), code = index code i_list in
     (* extend the environment [env] with input and output variables *)
     let env, code = List.fold_left (in_out ix) (env, code) i_list in
     let { mem = m_code; init = i_code; instances = j_code;
	   reset = r_code; step = s_code } =
       block env (ix :: loop_path) b_eq_list in
     (* transforms instances into arrays *)
     let j_code = State.map (array_of_instance (plus (minus e2 e1) one)) j_code in
     let m_code = State.map (array_of_memory (plus (minus e2 e1) one)) m_code in
     (* generate the initialization code *)
     let initialization_list,
	 { mem = m; instances = j; init = i; reset = r; step = s } =
       Misc.map_fold init code init_list in
     { mem = State.seq m_code m; instances = State.seq j_code j;
       init = sequence (for_loop true ix e1 e2 i_code) i;
       reset = sequence (for_loop true ix e1 e2 r_code) r;
       step = sequence (Osequence initialization_list)
			(sequence (for_loop true ix e1 e2 s_code) s) }
  | Zelus.EQbefore(before_eq_list) ->
     equation_list env loop_path before_eq_list code
  | Zelus.EQand _ | Zelus.EQblock _ | Zelus.EQnext _
  | Zelus.EQder _ | Zelus.EQemit _ | Zelus.EQautomaton _ 
  | Zelus.EQpresent _ -> assert false
				
and equation_list env loop_path eq_list code =
  List.fold_right (fun eq code -> equation env loop_path eq code) eq_list code
		  
(* Translation of a math/with handler. *)
and match_handlers env loop_path p_h_list =
  let body code { Zelus.m_pat = p; Zelus.m_body = b; Zelus.m_env = m_env } =
    let env, mem_acc, var_acc = append loop_path m_env env in
    let { mem = m_code; step = s_code } as b_code =  block env loop_path b in
    { w_pat = pattern p; w_body = letvar var_acc s_code },
    seq code
	{ b_code with step = Osequence []; mem = State.seq mem_acc m_code } in
  Misc.map_fold body empty_code p_h_list
	  
and local env loop_path { Zelus.l_eq = eq_list; Zelus.l_env = l_env } e =
  let env, mem_acc, var_acc = append loop_path l_env env in
  let e, code = exp env loop_path empty_code e in
  let { mem = m_code; step = s_code } as eq_code =
    equation_list env loop_path eq_list { code with step = Oexp(e) } in
  { eq_code with mem = State.seq mem_acc m_code; step = letvar var_acc s_code }

and block env loop_path { Zelus.b_body = eq_list; Zelus.b_env = n_env  } =
  let env, mem_acc, var_acc = append loop_path n_env env in
  let { mem = m_code; step = s_code } as eq_code =
    equation_list env loop_path eq_list empty_code in
  { eq_code with mem = State.seq mem_acc m_code;
		 step = letvar var_acc s_code }

         
(* Define a function or a machine according to a kind [k] *)
let machine n k pat_list { mem = m; instances = j; reset = r; step = s } =
  let k = Interface.kindtype k in
  match k with
  | Deftypes.Tstatic _ | Deftypes.Tany
  | Deftypes.Tdiscrete(false) -> Oletfun(n, pat_list, s)
  | Deftypes.Tdiscrete(true) | Deftypes.Tcont ->
    (* the [n-1] parameters are static *)
    let pat_list, p = Misc.firsts pat_list in
    let body =
       { ma_kind = k;
	 ma_params = pat_list;
	 ma_memories = State.list [] m;
	 ma_instances = State.list [] j;
	 ma_methods = 
	   [ { me_name = Oreset; me_params = []; me_body = r };
	     { me_name = Ostep; me_params = [p]; me_body = s } ] } in
     Oletmachine(n, body)
 
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
  | Zelus.Eopen(n) -> Oopen(n)
  | Zelus.Etypedecl(n, params, ty_decl) ->
     Otypedecl([n, params, type_of_type_decl ty_decl])
  | Zelus.Econstdecl(n, e) ->
     (* There should be no memory allocated by [e] *)
     let { step = s } = expression Env.empty e in
     Oletvalue(n, s)
  | Zelus.Efundecl(n, { Zelus.f_kind = k; Zelus.f_args = pat_list;
			Zelus.f_body = e; Zelus.f_env = f_env }) ->
     let env, mem_acc, var_acc = append empty_path f_env Env.empty in
     let pat_list = List.map pattern pat_list in
     let code = expression env e in
     machine n k pat_list code
	     
let implementation_list impl_list = Misc.iter implementation impl_list
