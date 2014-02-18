(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
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

(* The constant false *)
let cfalse = make (Oconst(Obool(false)))

(* the translation function returns a sequence of instructions of the *)
(* following form *)
type eq =
    | Let of pattern * exp
    | Match of exp * match_handler list
    | If of exp * exp
    | Letvar of Ident.t * Deftypes.typ * exp option
    | Set of Ident.t * sort * exp
    | Imp of exp
            
type code =
    { mem: (Ident.t * (Deftypes.typ * exp option)) State.t;
                   (* set of state variables, statically allocated *)
                   (* and possibly initialized with constant values *)
      inst: (Ident.t * Lident.t) State.t; (* set of instances *)
      eqs: eq State.t;  (* sequence of equations executed on a step *)
      init: eq State.t; (* sequence of code to execute on a reset *)
    }
    
let empty = { mem = State.empty; inst = State.empty; 
              eqs = State.empty; init = State.empty }
let pair { mem = m1; inst = i1; eqs = eqs1; init = init1 }
    { mem = m2; inst = i2; eqs = eqs2; init = init2 } =
  { mem = State.pair m1 m2; inst = State.pair i1 i2;
    eqs = State.pair eqs1 eqs2; init = State.pair init1 init2 }
let flush { mem = m1; inst = i1; eqs = eqs1; init = init1 } =
  State.list [] m1, State.list [] i1, State.list [] eqs1, State.list [] init1

(* environment that give the status of variables *)
type vars = { v_shared: S.t; v_mem: S.t }

let novars = { v_shared = S.empty; v_mem = S.empty }

let append { v_shared = s1; v_mem = m1 } { v_shared = s2; v_mem = m2 } =
  { v_shared = S.union s1 s2; v_mem = S.union m1 m2 }

let is_shared n { v_shared = shared } = S.mem n shared

let status_of_var n { v_shared = shared; v_mem = mem } =
  if S.mem n shared then Var else if S.mem n mem then Mem else Val

(** Translation of immediate values *)
let immediate = function
  | Deftypes.Eint(i) -> Oint(i)
  | Deftypes.Efloat(f) -> Ofloat(f)
  | Deftypes.Ebool(b) -> Obool(b)
  | Deftypes.Echar(c) -> Ochar(c)
  | Deftypes.Estring(s) -> Ostring(s)
  | Deftypes.Evoid -> Ovoid

(* compute the status of variables (either shared or memory) *)
let build eq_list =
  let rec buildrec 
      ({ v_shared = s; v_mem = m } as vars) { Zelus.eq_desc = desc } =
    match desc with
      (* variables written in several branches are shared *)
      | Zelus.EQmatch(_, _, p_h_list) ->
        let s = 
          List.fold_left
            (fun acc { Zelus.m_body = { Zelus.b_write = { dv = w } } } -> 
              S.union w acc)
            s p_h_list in
        { v_shared = s; v_mem = m }
      (* [x = pre(e)] or [x = v fby e] or [init x = e] or [next x = e] *)
      (* for a memory *)
      | Zelus.EQnext({Zelus.p_desc = Zelus.Evarpat(n)}, _, _)
      | Zelus.EQinit({Zelus.p_desc = Zelus.Evarpat(n)}, _, _)
      | Zelus.EQeq({Zelus.p_desc = Zelus.Evarpat(n)}, 
                   {Zelus.e_desc = Zelus.Eapp((Zelus.Eunarypre 
                                                  | Zelus.Efby),_)})
        -> { v_shared = s; v_mem = S.add n m }
      | Zelus.EQreset({ Zelus.b_write = { dv = w } }, _) -> 
          { v_shared = S.union w s; v_mem = m }
      | _ -> vars
  and buildlist vars eq_list =
    List.fold_left buildrec vars eq_list in
  buildlist novars eq_list

let add_localvar { v_shared = shared } env ctx =
  let addrec n acc = 
    (* initialize the shared variable with [im] when its kind *)
    (* is ValDefault(im) in the source. Otherwise, initialize with any value *)
    try
      let { t_sort = k; t_typ = ty } = Env.find n env in
      let opt_e = 
        match k with 
          | ValDefault(im) -> Some(make (Oconst(immediate im))) | _ -> choose ty in
      State.cons (Letvar(n, ty, opt_e)) acc
    with
      | Not_found -> failwith (Ident.name n) in
  { ctx with eqs = S.fold addrec shared ctx.eqs }

let void = make (Oconst(Ovoid))
  
let letin eq_list e =
  let rec letrec = function
    | [] -> e
    | Let(p, e) :: eq_list -> 
        make (Olet([p, e], letrec eq_list))
    | Set(n, k, e) :: eq_list -> 
        make (Osequence(make(Oassign(n, k, e)), letrec eq_list))
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
              
let machine pat_list ctx e =
  let mems, insts, eqs, inits = flush ctx in
  { m_memories = mems; m_instances = insts;
    m_step = (pat_list, letin eqs e); m_reset = letin inits void} 
 
(** Conditional. [p = e1 every z1 | ... default e] is translated into *)
(* [p = if z1 then e1 else ... else e] *)
let ifthenelse e1 e2 e3 = make (Oifthenelse(e1, e2, e3))

(** Execute the set of initialization function when a condition is true *)
let reset e init eqs =
  let init = State.list [] init in
  match init with 
    | [] -> eqs 
    | _ -> State.cons (If(e, letin init void)) eqs

let rec default e_e_list e =
  match e_e_list with
    | [] -> e
    | (e1, z1) :: e_e_list -> ifthenelse z1 e1 (default e_e_list e)

(* reset application. When [e_opt = Some(e)] the application is reset *)
let apply ctx e_opt op e_list =
  if Types.is_a_node op
  then
    (* create an object *)
    let id = Ident.fresh "inst" in
    let ctx = 
      { ctx with inst = State.cons (id, op) ctx.inst;
        init = State.cons (Imp(make(Oreset(op, id)))) ctx.init } in
    let e = 
      match e_opt with
	| None -> make (Ostep(op, id, e_list))
	| Some(e) ->
	    make (Osequence(make(Oifthenelse(e, make(Oreset(op, id)), void)),
			    make (Ostep(op, id, e_list)))) in
    ctx, e
  else ctx, make (Oapp(op, e_list))

(** Translation of expressions. [vars] is the set of shared variables *)
let rec exp vars { Zelus.e_desc = desc } =
  match desc with
    | Zelus.Econst(i) -> empty, make (Oconst(immediate i))
    | Zelus.Elocal(n) -> 
        (* [n] is shared is if appears in [vars.v_shared]; a state variable *)
        (* if it appears in [vars.v_mem] and a value otherwise *)
        empty, make (Olocal(n, status_of_var n vars))
    | Zelus.Elast(n) -> empty, make (Olocal(n, Mem))
    | Zelus.Eglobal(ln) -> empty, make (Oglobal(ln))
    | Zelus.Econstr0(ln) -> empty, make (Oconstr0(ln))
    | Zelus.Etuple(e_list) ->
        let ctx, e_list = exp_list vars e_list in
        ctx, make (Otuple(e_list))
    | Zelus.Eapp(Zelus.Eifthenelse, [e1; e2; e3]) ->
        let ctx1, e1 = exp vars e1 in
        let ctx2, e2 = exp vars e2 in
        let ctx3, e3 = exp vars e3 in
        pair ctx1 (pair ctx2 ctx3), make (Oifthenelse(e1, e2, e3))
    | Zelus.Erecord(label_e_list) ->
        let ctx, label_e_list = record_list vars label_e_list in
        ctx, make (Orecord(label_e_list))
    | Zelus.Erecord_access(e, longname) ->
        let ctx, e = exp vars e in
        ctx, make (Orecord_access(e, longname))
    | Zelus.Etypeconstraint(e, ty) ->
        let ctx, e = exp vars e in
        ctx, make (Otypeconstraint(e, type_expression ty))
    | Zelus.Elet(l, e) ->
        let vars, ({ eqs = eqs } as ctx) = local vars l in
        let ctx_e, e = exp vars e in
        pair { ctx with eqs = State.empty } ctx_e, 
        letin (State.list [] eqs) e
    | Zelus.Eseq(e1, e2) ->
        let ctx1, e1 = exp vars e1 in
        let ctx2, e2 = exp vars e2 in
        pair ctx1 ctx2, make (Osequence(e1, e2))
    | Zelus.Eapp(Zelus.Eop(op), e_list) ->
        let ctx, e_list = exp_list vars e_list in
	apply ctx None op e_list
    | Zelus.Eapp(Zelus.Eevery(op), e :: e_list) ->
        let ctx_e, e = exp vars e in
	let ctx, e_list = exp_list vars e_list in
	apply (pair ctx_e ctx) (Some(e)) op e_list
    | Zelus.Eapp _ | Zelus.Eperiod _ 
    | Zelus.Epresent _ | Zelus.Ematch _ -> assert false

and exp_list vars e_list =
  match e_list with
    | [] -> empty, []
    | e :: e_list ->
        let ctx_e, e = exp vars e in
        let ctx, e_list = exp_list vars e_list in
        pair ctx_e ctx, e :: e_list

and record_list vars label_e_list =
  match label_e_list with
    | [] -> empty, []
    | (label, e) :: label_e_list ->
        let ctx, e = exp vars e in
        let ctx_label_list, label_e_list = record_list vars label_e_list in
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
and equation vars { Zelus.eq_desc = desc } =
  match desc with
    | Zelus.EQeq({ Zelus.p_desc = Zelus.Evarpat(n) }, 
                  { Zelus.e_desc = Zelus.Eapp(Zelus.Eunarypre, [e]);
                    Zelus.e_typ = ty }) ->
        let some_v = choose ty in
        let ctx, e = exp vars e in
        (* a reset is useless *)
        { ctx with eqs = State.cons (Set(n, Mem, e)) ctx.eqs;
                   mem = State.cons (n, (ty, some_v)) ctx.mem }
    | Zelus.EQeq({ Zelus.p_desc = Zelus.Evarpat(n) },
                  { Zelus.e_desc = Zelus.Eapp(Zelus.Efby,[v; e]);
                    Zelus.e_typ = ty }) ->
        let ctx1, v = exp vars v in
        let ctx2, e = exp vars e in
        let ctx = pair ctx1 ctx2 in
          (* a reset is done for initialized delays only *)
          { ctx with eqs = State.cons (Set(n, Mem, e)) ctx.eqs;
                   init = State.cons (Set(n, Mem, v)) ctx.init;
                   mem = State.cons (n, (ty, Some(v))) ctx.mem }
    | Zelus.EQeq({ Zelus.p_desc = Zelus.Evarpat(n) }, e) 
        when is_shared n vars ->
        let ctx, e = exp vars e in
        { ctx with eqs = State.cons (Set(n, Var, e)) ctx.eqs }
    | Zelus.EQeq(pat, e) ->
        let ctx, e = exp vars e in
        let pat = pattern pat in
        { ctx with eqs = State.cons (Let(pat, e)) ctx.eqs }
    | Zelus.EQmatch(_, e, p_h_list) ->
        let ctx_e, e = exp vars e in
        let ctx, p_h_list = match_handlers vars p_h_list in
        let ctx = pair ctx_e ctx in
        { ctx with eqs = State.cons (Match(e, p_h_list)) ctx.eqs }
    | Zelus.EQreset(b, e) ->
        let ctx_e, e = exp vars e in
        let ({ init = init } as ctx) = block vars b in
        (* execute the initialization code when [e] is true *)
        let ctx = pair ctx_e ctx in
        { ctx with eqs = reset e init ctx.eqs }
    | Zelus.EQinit _ | Zelus.EQnext _ | Zelus.EQder _ 
    | Zelus.EQemit _ | Zelus.EQautomaton _ 
    | Zelus.EQpresent _ -> assert false
        
and equation_list vars = function
  | [] -> empty
  | eq :: eq_list -> 
      let ctx_eq = equation vars eq in
      let ctx = equation_list vars eq_list in
      pair ctx_eq ctx

and handler_list vars = function
  | [] -> empty, []
  | (e, ze) :: h_list ->
      let ctx_e, e = exp vars e in
      let ctx_ze, ze = exp vars ze in
      let ctx, h_list = handler_list vars h_list in
      pair ctx_e (pair ctx_ze ctx), (e, ze) :: h_list

and match_handlers vars p_h_list =
  match p_h_list with
    | [] -> empty, []
    | { Zelus.m_pat = p; Zelus.m_body = b } :: p_h_list ->
        let ctx, p_h_list = match_handlers vars p_h_list in
        let ({ eqs = eqs } as ctx_b) = block vars b in
        pair ctx { ctx_b with eqs = State.empty }, 
        { w_pat = pattern p; w_body = letin (State.list [] eqs) void } 
        :: p_h_list

and local vars { Zelus.l_eq = eq_list; Zelus.l_env = env } =
  (* first compute the status of variables in eq_list *)
  let vars0 = build eq_list in
  let vars = append vars0 vars in
  let ctx = equation_list vars eq_list in
  (* for every shared variable, add a local declaration *)
  (* according to their status in the environment *)
  vars, add_localvar vars0 env ctx

and block vars { Zelus.b_body = eq_list; Zelus.b_env = n_env  } =
  (* we look at the status of locally defined variables from [l_list] *)
  (* in [eq_list] to know which is shared or not *)
  let vars0 = build eq_list in
  let vars = append vars0 vars in
  (* add [let x1 = e1 in ... let xn = en] for variables in [n_env] *)
  let eqs = 
    Env.fold
      (fun n { t_typ = ty } acc ->
        if is_shared n vars then State.cons (Letvar(n, ty, choose ty)) acc else acc)
      n_env State.empty in
  let ctx = { empty with eqs = eqs } in
  (* then translate the sequence of equations *)    
  let ctx_eq = equation_list vars eq_list in
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
        
let implementation { Zelus.desc = desc } =
  match desc with
      | Zelus.Eopen(n) -> make (Oopen(n))
      | Zelus.Etypedecl(n, params, ty_decl) ->
          make (Otypedecl([n, params, type_of_type_decl ty_decl]))
      | Zelus.Econstdecl(n, e) ->
          let _, e = exp novars e in
          make (Oletvalue(n, e))
      | Zelus.Efundecl(n, { Zelus.f_kind = Zelus.D;
                             Zelus.f_args = pat_list;
                             Zelus.f_body = e }) ->
          let pat_list = List.map pattern pat_list in
          let ctx, e = exp novars e in
          make (Oletmachine(n, machine pat_list ctx e))
      | Zelus.Efundecl(n, { Zelus.f_args = pat_list; Zelus.f_body = e }) ->
          let pat_list = List.map pattern pat_list in
          let _, e = exp novars e in
          make (Oletfun(n, pat_list, e))

let implementation_list impl_list = Misc.iter implementation impl_list
