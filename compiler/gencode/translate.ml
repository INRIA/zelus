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
(* translation from normalized scheduled data-flow code to obc *)
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
type env = sort Ident.Env.t (* the symbol table *)

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
      inst: (Ident.t * Lident.t * Deftypes.kind) State.t; (* set of instances *)
      reset: eq State.t; (* sequence of equations for resetting the block *)
      step: eq State.t; (* sequence of equations during the discrete step *)
      }

let empty = { mem = State.empty; init = State.empty; inst = State.empty; 
	      reset = State.empty; step = State.empty }

let pair { mem = m1; init = in1; inst = i1; reset = r1; step = d1 } 
	 { mem = m2; init = in2; inst = i2; reset = r2; step = d2 } =
  { mem = State.par m1 m2; init = State.par in1 in2;
    inst = State.par i1 i2; reset = State.par r1 r2; 
    step = State.par d1 d2 }

let flush 
      { mem = m1; init = in1; inst = i1; reset = r1; step = s1 } =
  (* associate an initial value to state variables *)
  let initialize table (n, mem, ty) =
    let opt_e = try Some(Env.find n table)
		with Not_found -> choose ty in
    (n, (mem, ty, opt_e)) in
  let m1 = State.list [] m1 in
  let in1 = State.list [] in1 in
  let table = 
    List.fold_left (fun acc (n, e) -> Env.add n e acc) Env.empty in1 in
  let m1 = List.map (initialize table) m1 in
  m1, State.list [] i1, State.list [] r1, State.list [] s1


(* Extension of an environment. The environment is used to decide which *)
(* kind of assignment or read must be done on a variable *)
(* [append shared_variables zero_variables l_env env0 = l_mem, env] *)
(* returns the set of state variables *)
(* [l_mem] defined in [l_env] and a new environment [env] *)
(* [shared_variables] is the set of local names which are shared *)
(* [zero_variables] is the set of local names defined by en eq. [x = up(e)] *)
let append shared_variables zero_variables l_env env0 =
  (* for every entry in [l_env], add the name into the environment *)
  (* For names in [shared_variables], switch sort [Val] to [Var] *)
  let sort n { t_sort = sort; t_typ = typ } =
    let sort = match sort with
      | Deftypes.Val | Deftypes.ValDefault _ -> 
	  if S.mem n shared_variables then Var else Val
      | Deftypes.Mem 
	  { t_der_is_defined = der; t_last_is_used = is_last; 
	    t_initialized = is_init } ->
	 if der then Mem (Cont)
	 else if is_last || is_init then Mem Discrete
	 else if S.mem n shared_variables then Var else Val in
    sort, typ in
  (* add zero-crossing variables to [l_env] *)
  let zero n l_env = Env.add n (Mem(Zero), Initial.typ_bool) l_env in
  (* build the declaration of state variables *)
  let mem n (sort, typ) (l_shared, l_mem) =
    match sort with
    | Val -> l_shared, l_mem
    | Var -> S.add n l_shared, l_mem
    | Mem m -> l_shared, State.cons (n, m, typ) l_mem in
  let l_env = Env.mapi sort l_env in
  let l_env = S.fold zero zero_variables l_env in
  let l_shared, l_mem = Env.fold mem l_env (S.empty, State.empty) in
  l_shared, l_mem, Env.append l_env env0

let is_shared n env =  
  try
    let sort,_ = Env.find n env in
    match sort with | Var -> true | _ -> false
  with 
    | Not_found -> assert false

let is_derivative n env =  
  try
    let sort,_ = Env.find n env in
    match sort with 
    | Mem(Cont) -> true | Mem _ -> false | _ -> assert false
  with 
    | Not_found -> assert false

let sort n env =  
  try
    let sort,_ = Env.find n env in sort
  with 
    | Not_found -> assert false

(** Translation of a variable read. *)
let localvar n env =
  try
    let sort,_ = Env.find n env in
    match sort with
      | Val -> make (Olocal(n, false)) | Var -> make (Olocal(n, true))
      | Mem(m) ->
	 begin match m with
	 | Discrete -> make (Ostate(Oleft_state_name(n)))
	 | Zero -> 
	    make (Ostate((Oleft_state_primitive_access
					 (Oleft_state_name(n), Ozero_in))))
	 | Cont -> 
	    make (Ostate(Oleft_state_primitive_access(Oleft_state_name(n),
					  Ocontinuous)))
	 end
  with
  | Not_found -> Misc.internal_error "Unbound variable" Printer.name n

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
 
(* compute the set of shared variables and zero-crossing variables *)
(* from a sequence of equations. If a variable [x] has more than one *)
(* definition, it is considered as a shared variable *)
let variables eq_list =
  let rec buildrec (shared_variables, zero_variables) { Zelus.eq_desc = desc } =
    match desc with
    (* zero-crossing variables *)
    | Zelus.EQeq({ Zelus.p_desc = Zelus.Evarpat(n) },
		 { Zelus.e_desc = Zelus.Eapp(Zelus.Eup, _) }) ->
       shared_variables, S.add n zero_variables
    | Zelus.EQmatch(_, _, p_h_list) ->
       (* variables written in several branches are shared *)
       List.fold_left
         (fun acc { Zelus.m_body = { Zelus.b_write = { dv = w } } } -> 
          S.union w acc)
         shared_variables p_h_list, zero_variables
    | _ -> shared_variables, zero_variables
  and buildlist (shared_variables, zero_variables) eq_list =
    List.fold_left buildrec (shared_variables, zero_variables) eq_list in
  buildlist (S.empty, S.empty) eq_list

(* For every shared variable appearing in [l_env] add a local declaration *)
(* var x in ... *)
let add_localvar l_shared l_env ctx =
  let addrec n { t_sort = k; t_typ = ty } acc = 
    (* initialize the shared variable with [im] when its kind *)
    (* is ValDefault(c) in the source. Otherwise, initialize with any value *)
    if S.mem n l_shared then
      let opt_e = 
        match k with 
        | ValDefault(c) -> Some(constant c)
	| _ -> choose ty in
      State.cons (Letvar(n, ty, opt_e)) acc
    else acc in
  { ctx with step = Env.fold addrec l_env ctx.step }

(* Add the declaration of state variables *)
let add_memories l_mem ctx = { ctx with mem = State.par l_mem ctx.mem }

(* Turn equations produced during the translation into expressions from Obc *) 
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
let reset e init eqs =
  let init = State.list [] init in
  match init with 
    | [] -> eqs 
    | _ -> State.cons (If(e, letin init void)) eqs

(* Converts an initialisation [x, e] into an assignment *)
let init_to_eq env (x, e) =
  let left = 
    if is_derivative x env 
    then Oleft_state_primitive_access(Oleft_state_name x, Ocontinuous)
    else Oleft_state_name x in
  Setstate(left, e)
     
(** Translation of a function application. *)
(* It returns a context [ctx] and an expression *)
(* When [e_opt = Some(e)] the application is reset *)
let apply ctx e_opt op e_list =
  let k = Types.kind_of_node op in
  match k with
    | Deftypes.Tany | Deftypes.Tdiscrete(false) -> 
      let e = make (Oapp(op, e_list)) in ctx, e
    | Deftypes.Tdiscrete(true) | Deftypes.Tcont ->
      (* create an instance *)
      let id = Ident.fresh "inst" in
      let ctx = 
	{ ctx with inst = State.cons (id, op, k) ctx.inst;
		   reset = 
		     State.cons
		       (Imp(make(Omethod({ c_machine = op;
					   c_method_name = Oreset;
					   c_instance = Some(id) }, [])))) 
		       ctx.reset } in
      let e_step = 
	match e_opt with
	| None -> make (Omethod({ c_machine = op; c_method_name = Ostep;
				  c_instance = Some(id) }, e_list))
	| Some(e) ->
	   make (Osequence(
		     make(Oifthenelse(e, 
				      make(Omethod({ c_machine = op;
						     c_method_name = Oreset;
						     c_instance = Some(id) },
						   [])), 
				      void)),
		     make (Omethod({ c_machine = op;
				     c_method_name = Ostep;
				     c_instance = Some(id) }, e_list)))) in
      ctx, e_step

(** Translation of expressions under an environment [env] *)
let rec exp env { Zelus.e_desc = desc } =
  match desc with
    | Zelus.Econst(i) -> empty, make (Oconst(immediate i))
    | Zelus.Elocal(n) | Zelus.Elast(n) -> empty, localvar n env
    | Zelus.Eglobal(ln) -> empty, make (Oglobal(ln))
    | Zelus.Econstr0(ln) -> empty, make (Oconstr0(ln))
    | Zelus.Etuple(e_list) ->
       let ctx, e_list = exp_list env e_list in
       ctx, make (Otuple(e_list))
    | Zelus.Eapp(Zelus.Eifthenelse, [e1; e2; e3]) ->
       let ctx1, e1 = exp env e1 in
       let ctx2, e2 = exp env e2 in
       let ctx3, e3 = exp env e3 in
       pair ctx1 (pair ctx2 ctx3), make (Oifthenelse(e1, e2, e3))
    | Zelus.Erecord(label_e_list) ->
       let ctx, label_e_list = record_list env label_e_list in
       ctx, make (Orecord(label_e_list))
    | Zelus.Erecord_access(e, longname) ->
       let ctx, e = exp env e in
       ctx, make (Orecord_access(e, longname))
    | Zelus.Etypeconstraint(e, ty) ->
       let ctx, e = exp env e in
       ctx, make (Otypeconstraint(e, type_expression ty))
    | Zelus.Elet(l, e) ->
       (* [l] must be stateless and this is ensured by the normalization *)
       (* process *)
       let env, ({ step = eqs } as ctx) = local env l in
       let ctx_e, e = exp env e in
       pair { ctx with step = State.empty } ctx_e, 
       letin (State.list [] eqs) e
    | Zelus.Eseq(e1, e2) ->
       let ctx1, e1 = exp env e1 in
       let ctx2, e2 = exp env e2 in
       pair ctx1 ctx2, make (Osequence(e1, e2))
    | Zelus.Eapp(Zelus.Eup, [e]) -> exp env e
    | Zelus.Eapp(Zelus.Eop(_, op), e_list) ->
       let ctx, e_list = exp_list env e_list in
       let ctx, e_step = apply ctx None op e_list in
       ctx, e_step
    | Zelus.Eapp(Zelus.Eevery(_, op), e :: e_list) ->
       let ctx_e, e = exp env e in
       let ctx, e_list = exp_list env e_list in
       let ctx, e_step = apply (pair ctx_e ctx) (Some(e)) op e_list in
       ctx, e_step
    | Zelus.Eapp _ | Zelus.Eperiod _ 
    | Zelus.Epresent _ | Zelus.Ematch _ -> assert false

and exp_list env e_list =
  match e_list with
    | [] -> empty, []
    | e :: e_list ->
        let ctx_e, e = exp env e in
        let ctx, e_list = exp_list env e_list in
        pair ctx_e ctx, e :: e_list

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
     let ctx, e = exp env e in
     let assign =
       match sort n env with
       | Val -> Let(make (Ovarpat(n)), e)
       | Var -> Set(Oleft_name n, e)
       | Mem m -> 
	  match m with
	  | Zero -> Setstate(Oleft_state_primitive_access(Oleft_state_name(n), 
							  Ozero_out), e)
	  | Discrete -> Setstate(Oleft_state_name n, e)
	  | Cont -> Setstate(Oleft_state_primitive_access(Oleft_state_name(n),
							  Ocontinuous), e) in
     { ctx with step = State.cons assign ctx.step }
  | Zelus.EQset(ln, e) ->
      let ctx, e = exp env e in
      { ctx with step = 
		   State.cons (Setstate(Oleft_state_global(ln), e)) ctx.step }
  | Zelus.EQder(n, e, None, []) ->
     (* derivatives [der n = e] *)
     let ctx, e = exp env e in
     { ctx with step = 
		  State.cons 
		    (Setstate(Oleft_state_primitive_access(Oleft_state_name(n), 
							   Oderivative), e)) 
		    ctx.step }
  | Zelus.EQeq(pat, e) ->
     (* regular equation of local variables *)
     let ctx, e = exp env e in
     let pat = pattern pat in
     { ctx with step = State.cons (Let(pat, e)) ctx.step }
  | Zelus.EQmatch(_, e, p_h_list) ->
     let ctx_e, e = exp env e in
     let ctx, p_step_h_list = match_handlers env p_h_list in
     let ctx = pair ctx_e ctx in
     { ctx with step = State.cons (Match(e, p_step_h_list)) ctx.step }
  | Zelus.EQreset(res_eq_list, e) ->
     let ctx_e, e = exp env e in
     let ctx_res_eq_list = equation_list env res_eq_list in
     (* execute the initialization code when [e] is true *)
     let ctx_res_eq_list = 
       { ctx_res_eq_list with 
	 step = reset e (State.seq (State.map (init_to_eq env) 
				      ctx_res_eq_list.init)
			   ctx_res_eq_list.step) State.empty } in
     pair ctx_e ctx_res_eq_list
  | Zelus.EQinit(n, ({ Zelus.e_typ = ty } as v)) ->
     (* initialization of a register with an immediate value *)
     let is_immediate = Reset.static v in
     let ctx, v = exp env v in
     let n_receives_v = init_to_eq env (n, v) in
     if is_immediate
     then { ctx with reset = State.cons n_receives_v ctx.reset;
		     init = State.cons (n, v) ctx.init }
     else { ctx with step = State.cons n_receives_v ctx.step }
  | Zelus.EQnext _ | Zelus.EQder _ 
  | Zelus.EQemit _ | Zelus.EQautomaton _ 
  | Zelus.EQpresent _ | Zelus.EQblock _ -> assert false
				
and equation_list env = function
  | [] -> empty
  | eq :: eq_list -> 
     let ctx_eq = equation env eq in
     let ctx = equation_list env eq_list in
     pair ctx_eq ctx
	  
(* Translation of a math/with handler. *)
and match_handlers env p_h_list =
  match p_h_list with
  | [] -> empty, []
  | { Zelus.m_pat = p; Zelus.m_body = b; Zelus.m_env = m_env } :: p_h_list ->
     let ctx, p_step_h_list = match_handlers env p_h_list in
     let _, _, env = append S.empty S.empty m_env env in
     let ({ step = step } as ctx_b) = block env b in
     pair ctx { ctx_b with step = State.empty }, 
     { w_pat = pattern p; w_body = letin (State.list [] step) void } 
     :: p_step_h_list
	  
and local env { Zelus.l_eq = eq_list; Zelus.l_env = l_env } =
  (* first compute the sort of variables in eq_list *)
  let shared_variables, zero_variables = variables eq_list in
  let l_shared, l_mem, env = append shared_variables zero_variables l_env env in
  let ctx = equation_list env eq_list in
  (* for every shared variable, add a local declaration *)
  (* according to their status in the environment *)
  let ctx = add_localvar l_shared l_env ctx in
  (* add state variables *)
  let ctx = add_memories l_mem ctx in
  env, ctx

and block env { Zelus.b_body = eq_list; Zelus.b_env = n_env  } =
  (* we look at the status of locally defined variables from [l_list] *)
  (* in [eq_list] to know which is shared or not *)
  let shared_variables, zero_variables = variables eq_list in
  let l_shared, l_mem, env = 
    append shared_variables zero_variables n_env env in
  (* add [var x1 = e1 in ... var xn = en] for shared variables in [n_env] *)
  let ctx = add_localvar l_shared n_env empty in
  (* add state variables *)
  let ctx = add_memories l_mem ctx in
  (* then translate the sequence of equations *)    
  let ctx_eq = equation_list env eq_list in
  pair ctx ctx_eq

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
     let env, ctx = local env l in
     let ctx_e, e = exp env e_let in
     pair ctx ctx_e, e
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
         let l_shared, l_mem, env = append S.empty S.empty f_env Env.empty in
	 let pat_list = List.map pattern pat_list in
         let ctx, e = expression env e in
         let ctx = add_memories l_mem ctx in
	 machine n k pat_list ctx e      

let implementation_list impl_list = Misc.iter implementation impl_list
