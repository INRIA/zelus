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
(* translation from zelus code to obc *)
open Misc
open Ident
open Global
open Deftypes
open Obc

(* makes an initial value from a type. returns None when it fails *)
let choose ty =
  let tuple l = make (Otuple(l)) in
  let efalse = make (Oconst(Obool(false))) in
  let echar0 = make (Oconst(Ochar('a'))) in
  let ezero = make (Oconst(Oint(0))) in
  let efzero = make (Oconst(Ofloat(0.0))) in
  let estring0 = make (Oconst(Ostring(""))) in
  let evoid = make (Oconst(Ovoid)) in
  let rec value_from_deftype id =
    try
      let { info = { type_desc = ty_c } } = 
        Modules.find_type (Lident.Modname(id)) in
      match ty_c with
        | Variant_type({ qualid = qualid } :: _) ->
            make (Oconstr0(Lident.Modname(qualid)))
        | Abstract_type | Variant_type _ -> failwith ""
        | Record_type(l_list) ->
            make (Orecord(
              List.map 
                (fun { qualid = qualid; info = { label_res = ty } } -> 
                  (Lident.Modname(qualid), value ty)) l_list))
        | Abbrev(_, ty) -> value ty
    with
      | Not_found -> failwith ""
  and value ty =
    match ty.t_desc with
      | Tvar -> failwith ""
      | Tproduct(ty_l) -> tuple (List.map value ty_l)
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
  try
    Some(value ty)
  with
    | Failure _ -> None

(* Basic constants *)
let cfalse = make (Oconst(Obool(false)))
let void = make (Oconst(Ovoid))
let czero = make (Oconst(Oint(0)))

(* The translation uses an environment to store information about identifiers *)
type env = Deftypes.tentry Env.t (* the symbol table *)

(* the translation function returns a sequence of instructions of the *)
(* following form *)
type eq =
  | Let of pattern * exp
  | Match of exp * exp match_handler list
  | If of exp * exp
  | Letvar of Ident.t * Deftypes.typ * exp option
  | Set of left_value * exp
  | Setstate of left_state_value * exp
  | Imp of exp
            
type code =
    { mem: (Ident.t * mem * Deftypes.typ) State.t; (* set of state variables *)
      init: (Ident.t * exp) State.t; (* set of initializations among the above *)
      instances:
	(Ident.t * Lident.t * Deftypes.kind) State.t; (* set of instances *)
      reset: eq State.t; (* sequence of equations for resetting the block *)
      step: eq State.t; (* sequence of equations during the discrete step *)
      }

let empty = { mem = State.empty; init = State.empty; instances = State.empty; 
	      reset = State.empty; step = State.empty }

let seq { mem = m1; init = in1; instances = i1; reset = r1; step = d1 } 
	{ mem = m2; init = in2; instances = i2; reset = r2; step = d2 } =
  { mem = State.seq m1 m2; init = State.seq in1 in2;
    instances = State.par i1 i2; reset = State.seq r1 r2; 
    step = State.seq d1 d2 }

let flush 
      { mem = m1; init = in1; instances = i1; reset = r1; step = s1 } =
  (* associate an initial value to state variables *)
  let initialize table (n, mem, ty) =
    let opt_e = try Some(Env.find n table) with Not_found -> choose ty in
    (n, (mem, ty, opt_e)) in
  let m1 = State.list [] m1 in
  let in1 = State.list [] in1 in
  let table = 
    List.fold_left (fun acc (n, e) -> Env.add n e acc) Env.empty in1 in
  let m1 = List.map (initialize table) m1 in
  m1, State.list [] i1, State.list [] r1, State.list [] s1

(** Translation of immediate values *)
let immediate = function
  | Deftypes.Eint(i) -> Oint(i)
  | Deftypes.Efloat(f) -> Ofloat(f)
  | Deftypes.Ebool(b) -> Obool(b)
  | Deftypes.Echar(c) -> Ochar(c)
  | Deftypes.Estring(s) -> Ostring(s)
  | Deftypes.Evoid -> Ovoid

let constant = function
  | Deftypes.Cimmediate(i) -> make (Oconst(immediate i))
  | Deftypes.Cglobal(ln) -> make (Oglobal(ln))

(* extend an environment *)
let append l_env env =
  (* convert a memory from Zelus into a memory from Obc *)
  let mem k_opt =
    match k_opt with
    | None -> Discrete
    | Some(k) ->
       match k with
       | Deftypes.Cont -> Cont
       | Deftypes.Zero -> Zero
       | Deftypes.Horizon -> Horizon
       | Deftypes.Period -> Period
       | Deftypes.Encore -> Encore in					
  (* add a memory variable for every state variable in [l_env] *)
  (* and a [letvar] declaration for every shared variable *)
  let addrec n { t_sort = k; t_typ = ty } (mem_acc, letval_acc) =
    (* initialize the shared variable with [im]. Otherwise, initialize *)
    (* with any value *)
    match k with
    | Sval -> mem_acc, letval_acc
    | Svar { v_default = v_opt } ->
       mem_acc,
       State.cons (Letvar(n, ty, Misc.optional_map constant v_opt)) letval_acc
    | Smem { m_kind = k_opt } ->
       State.cons (n, mem k_opt, ty) mem_acc, letval_acc in
  let env = Env.append l_env env in
  let mem_acc, letvar_acc = Env.fold addrec l_env (State.empty, State.empty) in
  { empty with mem = mem_acc; step = letvar_acc }, env
  
(* read and set of a state variable. *)
let kind is_read n k =
  match k with
  | None -> Oleft_state_name(n)
  | Some(k) ->
     match k with
     | Deftypes.Cont -> Oleft_state_primitive_access (Oleft_state_name(n), Ocont)
     | Deftypes.Zero ->
	Oleft_state_primitive_access (Oleft_state_name(n),
				      if is_read then Ozero_in else Ozero_out)
     | Deftypes.Horizon | Deftypes.Period | Deftypes.Encore -> Oleft_state_name(n)
							      
(** Translation of a variable read. *)
let local_var n env =
  let { t_sort = sort } =
    try Env.find n env
    with Not_found -> Misc.internal_error "Unbound variable" Printer.name n in
  match sort with
  | Sval -> make (Olocal(n, false))
  | Svar _ -> make (Olocal(n, true))
  | Smem { m_kind = k } -> make (Ostate(kind true n k))
	
		 
(* Turn equations produced during the translation into an Obc expression *) 
let letin eq_list e =
  let rec letrec = function
    | [] -> e
    | Let(p, e) :: eq_list -> 
        make (Olet([p, e], letrec eq_list))
    | Set(left, e) :: eq_list -> 
        make (Osequence(make(Oassign(left, e)), letrec eq_list))
    | Setstate(left, e) :: eq_list -> 
        make (Osequence(make(Oassign_state(left, e)), letrec eq_list))
    | Letvar(n, ty, opt_e) :: eq_list ->
        make (Oletvar(n, ty, opt_e, letrec eq_list))
    | If(e, e1) :: eq_list -> 
        make (Osequence(make(Oifthenelse(e, e1, void)), letrec eq_list)) 
    | Match(e, 
            [{ w_pat = { desc = Oconstpat(Obool(true)) }; w_body = e1}; 
             { w_pat = { desc = (Oconstpat(Obool(false)) | Owildpat) }; 
               w_body = e2 }]) :: eq_list -> 
        make (Osequence(make(Oifthenelse(e, e1, e2)), letrec eq_list))
    | Match(e, p_e_list) :: eq_list -> 
        make (Osequence(make(Omatch(e, p_e_list)), letrec eq_list))
    | Imp(e) :: eq_list ->
        make (Osequence(e, letrec eq_list)) in
  letrec eq_list
           
(* Execute the set of initialization function when a condition is true *)
(* This is only useful if the reset/every construct is kept up to translation *)
let reset e ({ reset = r } as ctx) =
  if State.is_empty r then ctx
  else { ctx with step =
		    State.cons (If(e, letin (State.list [] r) void)) ctx.step }
		      
(** Translation of a function application (f [every e_opt] (e1,...,en)) *)
(* Returns a context [ctx] and an expression *)
let apply e_opt op e_list =
  let k = Types.kind_of_node op in
  match k with
  | Deftypes.Tany
  | Deftypes.Tdiscrete(false) -> empty, make (Oapp(op, e_list))
  | Deftypes.Tdiscrete(true)
  | Deftypes.Tcont ->
     (* create an instance *)
     let id = Ident.fresh "i" in
     let reset_code =
       Imp(make(Omethod({ c_machine = op; c_method_name = Oreset;
			  c_instance = Some(id) }, []))) in
     let ctx = 
       { empty with instances = State.singleton (id, op, k);
		    reset = State.singleton reset_code } in
     let e_step = make (Omethod({ c_machine = op; c_method_name = Ostep;
				  c_instance = Some(id) }, e_list)) in
     (* reset the instance when [e_opt] is true *)
     match e_opt with
     | None -> ctx, e_step
     | Some(e) -> reset e ctx, e_step

(** Translation of expressions under an environment [env] *)
let rec exp env { Zelus.e_desc = desc } =
  match desc with
    | Zelus.Econst(i) -> empty, make (Oconst(immediate i))
    | Zelus.Elocal(n) | Zelus.Elast(n) -> empty, local_var n env
    | Zelus.Eglobal(ln) -> empty, make (Oglobal(ln))
    | Zelus.Econstr0(ln) -> empty, make (Oconstr0(ln))
    | Zelus.Etuple(e_list) ->
       let ctx, e_list = exp_list env e_list in
       ctx, make (Otuple(e_list))
    | Zelus.Erecord(label_e_list) ->
       let ctx, label_e_list = record_list env label_e_list in
       ctx, make (Orecord(label_e_list))
    | Zelus.Erecord_access(e, longname) ->
       let ctx, e = exp env e in
       ctx, make (Orecord_access(e, longname))
    | Zelus.Etypeconstraint(e, ty) ->
       let ctx, e = exp env e in
       ctx, make (Otypeconstraint(e, type_expression ty))
    | Zelus.Eapp((Zelus.Eup | Zelus.Ehorizon), [e]) -> exp env e
    | Zelus.Eapp(Zelus.Eafter, e :: _) -> exp env e
    | Zelus.Eapp(Zelus.Eifthenelse, [e1; e2; e3]) ->
       let ctx1, e1 = exp env e1 in
       let ctx2, e2 = exp env e2 in
       let ctx3, e3 = exp env e3 in
       seq ctx1 (seq ctx2 ctx3), make (Oifthenelse(e1, e2, e3))
    | Zelus.Eapp(Zelus.Eop(_, op), e_list) ->
       let ctx1, e_list = exp_list env e_list in
       let ctx2, e_step = apply None op e_list in
       seq ctx1 ctx2, e_step
    | Zelus.Eapp(Zelus.Eevery(_, op), e :: e_list) ->
       let ctx_e, e = exp env e in
       let ctx, e_list = exp_list env e_list in
       let ctx_op, e_step = apply (Some(e)) op e_list in
       seq ctx_e (seq ctx ctx_op), e_step
    | Zelus.Elet _ | Zelus.Eseq _ | Zelus.Eapp _ | Zelus.Eperiod _ 
    | Zelus.Epresent _ | Zelus.Ematch _ -> assert false

and exp_list env e_list =
  match e_list with
    | [] -> empty, []
    | e :: e_list ->
        let ctx_e, e = exp env e in
        let ctx, e_list = exp_list env e_list in
        seq ctx_e ctx, e :: e_list

and record_list env label_e_list =
  match label_e_list with
    | [] -> empty, []
    | (label, e) :: label_e_list ->
        let ctx, e = exp env e in
        let ctx_label_list, label_e_list = record_list env label_e_list in
        empty, (label, e) :: label_e_list

(** Patterns *)
and pattern { Zelus.p_desc = desc } =
  match desc with
  | Zelus.Ewildpat -> make (Owildpat)
  | Zelus.Econstpat(im) -> make (Oconstpat(immediate im))
  | Zelus.Econstr0pat(c0) -> make (Oconstr0pat(c0))
  | Zelus.Etuplepat(p_list) -> make (Otuplepat(List.map pattern p_list))
  | Zelus.Evarpat(n) -> make (Ovarpat(n))
  | Zelus.Erecordpat(label_pat_list) ->
     make (Orecordpat(List.map (fun (label, pat) -> (label, pattern pat))
			       label_pat_list))
  | Zelus.Etypeconstraintpat(p, ty) ->
     make (Otypeconstraintpat(pattern p, type_expression ty))
  | Zelus.Ealiaspat(p, n) ->
     make (Oaliaspat(pattern p, n))
  | Zelus.Eorpat(p1, p2) ->
     make (Oorpat(pattern p1, pattern p2))
	  
(** Equations *)
and equation env { Zelus.eq_desc = desc } =
  match desc with
  | Zelus.EQeq({ Zelus.p_desc = Zelus.Evarpat(n) }, e) ->
     let ctx_e, e = exp env e in
     let ctx_n = { empty with step = State.singleton (var_exp env n e) } in
     seq ctx_e ctx_n
  | Zelus.EQeq(p, e) ->
     (* regular equation of local variables *)
     let ctx_e, e = exp env e in
     let ctx_p = { empty with step = State.singleton (Let(pattern p, e)) } in
     seq ctx_e ctx_p
  | Zelus.EQset(ln, e) ->
      let ctx_e, e = exp env e in
      let ctx_ln =
	{ empty with step =
		       State.singleton (Setstate(Oleft_state_global(ln), e)) }
      in seq ctx_e ctx_ln
  | Zelus.EQder(n, e, None, []) ->
     (* derivatives [der n = e] *)
     let ctx_e, e = exp env e in
     let ctx_n =
       { empty with step =
		      State.singleton (Setstate(Oleft_state_primitive_access
						  (Oleft_state_name(n), Oder),
						e)) } in
     seq ctx_e ctx_n
  | Zelus.EQmatch(_, e, p_h_list) ->
     let ctx_e, e = exp env e in
     let ctx, p_step_h_list = match_handlers env p_h_list in
     let ctx_match =
       { empty with step = State.singleton (Match(e, p_step_h_list)) } in
     seq ctx_e (seq ctx ctx_match)
  | Zelus.EQreset(res_eq_list, e) ->
     let ctx_e, e = exp env e in
     let ctx_res_eq_list = equation_list env res_eq_list in
     (* execute the initialization code when [e] is true *)
     let ctx_res_eq_list = reset e ctx_res_eq_list in
     seq ctx_e ctx_res_eq_list
  | Zelus.EQinit(n, ({ Zelus.e_typ = ty } as e)) ->
     (* initialization of a state variable *)
     let is_immediate = Reset.static e in
     let ctx, e = exp env e in
     let n_receive_e = var_exp env n e in
     let ctx_r =
       if is_immediate then { empty with reset = State.singleton n_receive_e;
					 init = State.singleton (n, e) }
       else { empty with step = State.singleton n_receive_e } in
     seq ctx ctx_r
  | Zelus.EQblock(b) -> block env b
  | Zelus.EQnext _ | Zelus.EQder _ 
  | Zelus.EQemit _ | Zelus.EQautomaton _ 
  | Zelus.EQpresent _ -> assert false
				
and equation_list env eq_list =
  List.fold_left (fun ctx eq -> seq ctx (equation env eq)) empty eq_list

and var_exp env n e =
  let { t_sort = sort } = try Env.find n env with Not_found -> assert false in
  let assign =
    match sort with
    | Sval -> Let(make (Ovarpat(n)), e)
    | Svar _ -> Set(Oleft_name n, e)
    | Smem { m_kind = k } -> Setstate(kind false n k, e) in
  assign
    	  
(* Translation of a math/with handler. *)
and match_handlers env p_h_list =
  match p_h_list with
  | [] -> empty, []
  | { Zelus.m_pat = p; Zelus.m_body = b; Zelus.m_env = m_env } :: p_h_list ->
     let ctx, p_step_h_list = match_handlers env p_h_list in
     let ctx_env, env = append m_env env in
     let ({ step = step } as ctx_b) = block env b in
     seq ctx { ctx_b with step = State.empty }, 
     { w_pat = pattern p; w_body = letin (State.list [] step) void } 
     :: p_step_h_list
	  
and local (env, ctx) { Zelus.l_eq = eq_list; Zelus.l_env = l_env } =
  let ctx_l_env, env = append l_env env in
  let ctx = equation_list env eq_list in
  env, seq ctx_l_env ctx

and block env { Zelus.b_locals = l_list; Zelus.b_body = eq_list;
		Zelus.b_env = n_env  } =
  let ctx_n_env, env = append n_env env in
  let env, ctx = List.fold_left local (env, empty) l_list in
  let ctx_body = equation_list env eq_list in
  seq ctx_n_env (seq ctx ctx_body)

(** Translating type expressions *)
and type_expression { Zelus.desc = desc } =
  match desc with
    | Zelus.Etypevar(s) -> make (Otypevar(s))
    | Zelus.Etypeconstr(ln, ty_list) ->
        make (Otypeconstr(ln, List.map type_expression ty_list))
    | Zelus.Etypetuple(ty_list) ->
        make (Otypetuple(List.map type_expression ty_list))

and type_of_type_decl ty_decl =
  match ty_decl with
    | Zelus.Eabstract_type -> Oabstract_type
    | Zelus.Eabbrev(ty) -> Oabbrev(type_expression ty)
    | Zelus.Evariant_type(n_list) ->
        Ovariant_type(List.map (fun n -> Oconstr0decl(n)) n_list)
    | Zelus.Erecord_type(n_ty_list) ->
        Orecord_type(
          List.map (fun (n, ty) -> (n, type_expression ty)) n_ty_list)
        
(* Define a function or a machine according to a kind [k] *)
let machine n k pat_list ctx e =
  let k = Interface.kindtype k in
  let mems, insts, r_list, s_list = flush ctx in
  match k with
  | Deftypes.Tany | Deftypes.Tdiscrete(false) -> 
      make (Oletfun(n, pat_list, letin s_list e))
  | Deftypes.Tdiscrete(true) | Deftypes.Tcont ->
     let body =
       { m_kind = k;
	 m_memories = mems; m_instances = insts;
	 m_methods = 
	   [{ m_name = Oreset; m_param = []; m_body = letin r_list void };
	    { m_name = Ostep; m_param = pat_list; m_body = letin s_list e } ] } in
     make(Oletmachine(n, body))
 
(* Translation of an expression. After normalisation *)
(* the body of a function is either of the form [e] with [e] stateless *)
(* or [let Eq in e] with [e] stateless *)
let expression env ({ Zelus.e_desc = desc } as e) =
  match desc with
  | Zelus.Elet(l, e_let) ->
     let env, ctx = local (env, empty) l in
     let ctx_e, e = exp env e_let in
     seq ctx ctx_e, e
  | _ -> exp env e
       

(** Translation of a declaration *)
let implementation { Zelus.desc = desc } =
  match desc with
  | Zelus.Eopen(n) -> make (Oopen(n))
  | Zelus.Etypedecl(n, params, ty_decl) ->
     make (Otypedecl([n, params, type_of_type_decl ty_decl]))
  | Zelus.Econstdecl(n, e) ->
     (* There should be no memory allocated by [e] *)
     let { step = eqs }, e = expression Env.empty e in
     make (Oletvalue(n, letin (State.list [] eqs) e))
  | Zelus.Efundecl(n, { Zelus.f_kind = k;
			Zelus.f_args = pat_list; Zelus.f_body = e;
			Zelus.f_env = f_env }) ->
     let ctx_f_env, env = append f_env Env.empty in
     let pat_list = List.map pattern pat_list in
     let ctx, e = expression env e in
     machine n k pat_list (seq ctx_f_env ctx) e      
	     
let implementation_list impl_list = Misc.iter implementation impl_list
