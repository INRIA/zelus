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
(* Discretize the source code by removing ODEs. This turns the initial code *)
(* into valid synchronous code with extra inputs and outputs *)
(* Programs must be first normalized so that there is no more stateful *)
(* function calls inside expressions and all results are named. *)

open Misc
open Ident
open Zelus
open Global
open Deftypes

(* Principle of the translation. *)
(* A hybrid application [p = f(e1,...,en)] is turned into *)
(* [(upz, out_x, p) = f(d, zero, in_x, e1,...,en)] *)
(* [out_x] contains the vector of derivatives when [d = false] *)
(* and the vector of current values otherwise *)
(* A derivative [der x = e] is translated into [dx = e] *)
(* An initialization [init x = e] into [x = if d then pre(next_x) else in_x] *)
(* if next(x). [last_x = if d then pre(x) else in_x] if [x] is defined *)
(* [x = if d then pre(x) else in_x] otherwise *)
(* An equation [x = e] into [x = e]. An equation [next x = e] into [next_x = e] *)
(* [out_x = if d then x else dx] *)

(** The translation of a block/equation generates a value of type [ctx] *)
type ctx =
    { ctx_zero: (Ident.t * typ) State.t;
        (* the set of input zero-crossings computed by the solver *)
      ctx_upz: (Ident.t * typ) State.t;
        (* the set of output names to check for zero-crossing by the solver *)
      ctx_in_x: (Ident.t * typ) State.t;
        (* input values for the continuous state variables *)
      ctx_out_x: (Ident.t * typ) State.t;
        (* output instantaneous derivatives. *)
    }

let empty = 
  { ctx_zero  = State.empty; ctx_upz = State.empty;
    ctx_in_x = State.empty; ctx_out_x  = State.empty }

let pair 
  { ctx_zero = zv1; ctx_upz = up1; ctx_in_x = lv1; ctx_out_x = nx1 }
  { ctx_zero = zv2; ctx_upz = up2; ctx_in_x = lv2; ctx_out_x = nx2 }
    =
  { ctx_zero  = State.pair zv1 zv2; ctx_upz = State.pair up1 up2;
    ctx_in_x = State.pair lv1 lv2; ctx_out_x  = State.pair nx1 nx2 }

(** Merge of several contexes *)
let merge ctx_list = List.fold_left pair empty ctx_list

(* [discrete] is a parameter. [true] in the discrete mode; [false] in the *)
(* continuous mode *)
let discrete = Ident.fresh "d"

(** Build a renaming for every variable [x] defined by its instantaneous derivative *)
type renaming = 
    { der_name: Ident.t; in_name: Ident.t; out_name: Ident.t;
      last_name: Ident.t; next_name: Ident.t; is_set: bool; is_next: bool }

(** Basic functions for building terms *)
let typ_float = Initial.typ_float

let make desc ty = { e_desc = desc; e_loc = Location.no_location; e_typ = ty }
let czero = make (Econst (Efloat 0.0)) typ_float
let cunit = make (Econst Evoid) Initial.typ_unit
let ctrue = make (Econst (Ebool true)) Initial.typ_bool
let cfalse = make (Econst (Ebool false)) Initial.typ_bool

let var n ty = make (Elocal(n)) ty
let varpat n ty = 
  { p_desc = Evarpat(n); p_loc = Location.no_location; p_typ = ty }
let wildpat () = 
  { p_desc = Ewildpat; p_loc = Location.no_location; p_typ = no_typ }
let tuplepat l =
  match l with 
    | [] -> wildpat ()
    | [p] -> p 
    | l -> { p_desc  = Etuplepat(l); p_loc = Location.no_location;
             p_typ = Types.product (List.map (fun { p_typ = ty } -> ty) l) }
let tuple l =
  match l with 
    | [] -> cunit
    | [e] -> e 
    | l -> make (Etuple(l)) (Types.product (List.map (fun { e_typ = ty } -> ty) l))
  
let eqmake p e = { eq_desc = EQeq(p, e); eq_loc = Location.no_location }

let floatpat n = { p_desc = Evarpat(n); p_loc = Location.no_location; 
    p_typ = typ_float }
let boolpat n = { p_desc = Evarpat(n); p_loc = Location.no_location; 
    p_typ = Initial.typ_bool }
let unitpat = { p_desc = Econstpat(Evoid); p_loc = Location.no_location; 
    p_typ = Initial.typ_unit }
let boolvar n = make (Elocal(n)) Initial.typ_bool
let floatvar n = make (Elocal(n)) typ_float
let boolop op l = 
  make (Eapp(Eop(Lident.Modname(Initial.pervasives_name op)), l)) Initial.typ_bool
let floatop op l = 
  make (Eapp(Eop(Lident.Modname(Initial.pervasives_name op)), l)) typ_float
let pre e = make (Eapp(Eunarypre, [e])) e.e_typ

let is_ty_unit ty =
  match ty with
  | {t_desc = Tconstr(l, [], _)} -> l = Initial.unit_ident
  | _ -> false
let minusgreater e1 e2 = make (Eapp(Eminusgreater, [e1; e2])) e1.e_typ
let ifdiscrete e1 e2 = 
  make (Eapp(Eifthenelse, [boolvar discrete; e1; e2])) e1.e_typ

(* For every variable [x] which is defined by an equation [der x = ...] *)
(* we introduce five fresh names [in_x], [out_x], [last_x], [cur_x], [der_x] *)
(* [in_x]: input from the solveur; [out_x]: output for the solver *)
(* [last_x]: the left value of [x] *)
(* [cur_x]: the current value *)
(* [dx]: instantaneous derivative *)
(* The environment is changed so that [kind(x) = Mem] *)
let build_renaming n_list env = 
  let build x { t_sort = sort; t_typ = ty } (renaming0, n_list, env) =
    match sort with
      | Mem { t_initialized = false; t_last_is_used = mustlast; 
	      t_der_is_defined = true; t_is_set = is_set; t_next_is_set = n_set } -> 
          (* a derivative may not be initialized with an [init x = ...] *)
	  (* E.g. consider: *)
	  (* automaton | S1 -> do x = ... until... | S2 -> do der x = ... done *)
	  let in_x = Ident.fresh ("in" ^ (Ident.source x)) in
          let out_x = Ident.fresh ("out" ^ (Ident.source x)) in
          let dx = Ident.fresh ("d" ^ (Ident.source x)) in
          let last_x = Ident.fresh ("last" ^ (Ident.source x)) in
          let next_x = Ident.fresh ("next" ^ (Ident.source x)) in
          Env.add x
            { der_name = dx; in_name = in_x; out_name = out_x;
	      last_name = last_x; next_name = next_x; is_set = is_set; is_next = n_set }
	    renaming0,
	  dx :: (if n_set then next_x :: n_list else last_x :: n_list),
          Env.add x 
	    { t_sort = Mem { discrete_memory with t_last_is_used = false;
	                                          t_initialized = false };
	      t_typ = ty }
            (Env.add dx { t_sort = ValDefault(Efloat(0.0)); t_typ = ty } env)
      | Mem { t_initialized = true; t_last_is_used = mustlast;
	      t_der_is_defined = true; t_is_set = is_set; t_next_is_set = n_set } -> 
          let in_x = Ident.fresh ("in" ^ (Ident.source x)) in
          let out_x = Ident.fresh ("out" ^ (Ident.source x)) in
          let dx = Ident.fresh ("d" ^ (Ident.source x)) in
          let last_x = Ident.fresh ("last" ^ (Ident.source x)) in
          let next_x = Ident.fresh ("next" ^ (Ident.source x)) in
          Env.add x
	    { der_name = dx; in_name = in_x; out_name = out_x;
	      last_name = last_x; next_name = next_x; is_set = is_set; is_next = n_set }
	    renaming0,	  
          dx :: (if n_set then next_x :: n_list else last_x :: n_list),
          Env.add x 
	    { t_sort = Mem { discrete_memory with t_last_is_used = false;
	                                          t_initialized = false };
	      t_typ = ty }
            (Env.add (if n_set then next_x else last_x) 
	       { t_sort = Mem { discrete_memory with t_last_is_used = false;
	                                             t_initialized = false };
		 t_typ = ty }
	       (Env.add dx { t_sort = ValDefault(Efloat(0.0)); t_typ = ty } env))
      | _ -> renaming0, n_list, Env.add x { t_sort = sort; t_typ = ty } env in
  Env.fold build env (Env.empty, n_list, Env.empty)

(** Prepare extra inputs for all internal continuous state variables *)
let ctx_of_renaming renaming =
  let l_nx, l_lx = 
    Env.fold 
      (fun x { out_name = nx; in_name = lx } (l_nx, l_lx) -> 
        State.cons (nx, typ_float) l_nx, 
        State.cons (lx, typ_float) l_lx)
      renaming (State.empty, State.empty) in
  { empty with ctx_out_x = l_nx; ctx_in_x = l_lx }
    
(* add a list of equations [nx = ...] to [eq_list] *)
let add_equations_for_nx renaming eq_list =
  Env.fold 
    (fun x { der_name = dx; last_name = last_x; out_name = out_x; 
	     is_set = is_set; is_next = is_next } acc ->
      (* [out_x = if discrete then x else dx] *)
      (* if [is_set = is_next = false], add an equation [x = last_x] *)
      let acc =
	if is_set || is_next then acc 
	else (eqmake (floatpat x) (floatvar last_x)) :: acc in
      (eqmake (floatpat out_x) (ifdiscrete (floatvar x) (floatvar dx))) :: acc)
    renaming eq_list

(** Add [nx1:ty1;...;nxm:tym] and [upz1:ty'1;...;upzm:ty'm] *)
(** to a local environment *)
let env_of { ctx_out_x = l_nx; ctx_upz = l_upz } l_env =
  let default ty =
    if Types.is_a_float ty then ValDefault(Efloat(1.0)) else Val in
  (* first add derivatives [nx_1;...;nx_m] *)
  let l_env = 
    State.fold 
      (fun (id, ty) acc -> Env.add id { t_sort = Val; t_typ = ty } acc)
      l_nx l_env in
  (* then zero-crossings *)
  State.fold 
    (fun (id, ty) acc -> 
      Env.add id { t_sort = default ty; t_typ = ty } acc) l_upz l_env

(** How many elements (float/bool) are in my structure? *)
let size_of typ =
  let rec sizerec n ty =
    match ty.t_desc with
    | Tconstr(l, _, _) when l = Initial.unit_ident  -> n
    | Tconstr(l, _, _) when l = Initial.float_ident -> n + 1
    | Tconstr(l, _, _) when l = Initial.bool_ident -> n + 1
    | Tproduct(ty_list) -> List.fold_left sizerec n ty_list
    | Tlink ty -> sizerec n ty
    | _ -> assert false in
  sizerec 0 typ

let size_of_states info =
  match Global.cont_desc info with
  | Cflat _ -> assert false
  | Ctuple (ty_lx, ty_upz) -> size_of ty_upz, size_of ty_lx

(** Makes a default [0] value according to [ty] *)
let rec null ty =
  match ty.t_desc with
    | Tproduct(ty_list) -> tuple (List.map null ty_list)
    | Tlink ty -> null ty
    | Tconstr(l, _, _) when l = Initial.float_ident -> czero
    | Tconstr(l, _, _) when l = Initial.unit_ident -> cunit
    | _ -> assert false

let rec floats_to_bools ty =
  match ty.t_desc with
    | Tproduct(ty_list) ->
        {ty with t_desc = Tproduct (List.map floats_to_bools ty_list) }
    | Tlink ty -> floats_to_bools ty
    | Tconstr(l, _, _) when l = Initial.float_ident -> Initial.typ_bool
    | Tconstr(l, _, _) when l = Initial.unit_ident  -> ty
    | _ -> assert false

let different_state_repr_error loc name =
  Format.eprintf "%aHybrid node linking error: the function@%s@was \
                  not compiled with '-h dtuple'."
    Location.output_location loc
    (Lident.modname name);
  raise Misc.Error

(** Returns the type structure for zero-crossing and continuous states
 *  of a given function f. These types are reconstructed from the representative
 *  types stored in the module table.
 *
 *     typof ctx_in_x = typof ctx_dx
 *     typeof ctx_zero  ---replace bool by float---> typof ctx_upz
 *)
let concrete_type loc f =
  match Global.cont_desc (Modules.find_value f) with
  | Cflat _ -> different_state_repr_error loc f
  | Ctuple (ty_lx, ty_upz) ->
      let ty_z = floats_to_bools ty_upz in
      let ty_nx = ty_lx in
      (ty_z, ty_lx), (ty_upz, ty_nx)

(** Complement a block with equations [nx_1 = 0.0;...;nx_m = 0.0] for *)
(** every [nx_i] present in [l_nx] but not in [l_nx_local] of the current block *)
(** Invariant: when [nx in l_nx_local], it is already in [l_nx] *)
(** do it according to the type structure of [nx_i] *)
let complement { ctx_out_x = l_nx } { ctx_out_x = l_nx_local } ({ b_body = eq_list } as b)
    =
  (* local variables from [l_nx_local] *)
  let l_nx_local = 
    State.fold (fun (id, _) acc -> S.add id acc) l_nx_local S.empty in
  let eq_list = 
    State.fold 
      (fun (id, ty) acc -> 
        if S.mem id l_nx_local then acc 
	else (eqmake (varpat id ty) (null ty)) :: acc)
      l_nx eq_list in
  { b with b_body = eq_list }
                 
(** Translation of zero-crossings *)
(* According to flag [dzero], generate either a simple observation *)
(* of the zero-crossing detected by the solver or complete it with *)
(* a discrete zero-crossing *)
let up ctx e =
  let z = Ident.fresh "z" in
  let upz = Ident.fresh "upz" in
  { ctx with ctx_zero = State.cons (z, Initial.typ_bool) ctx.ctx_zero;
    ctx_upz  = State.cons (upz, typ_float) ctx.ctx_upz },
  (* (z or (d & (true -> ((pre e) * e <= 0) & (e >= 0)))) *)
  (if !Misc.dzero then
      (boolop ("||")
	 [(boolop ("&&")
	     [boolvar discrete;
	      boolop ("&&") [minusgreater ctrue 
			       (boolop ("<=") [pre(e); czero]); boolop (">") 
				 [e; czero]]]);
	  (var z Initial.typ_bool)])
   else (var z Initial.typ_bool)),
  (eqmake (floatpat upz) e)

(** Translation of an ODE: *)
(** [der x = e] produces [dx = e] *)
let der renaming loc x e eq_list =
  let { der_name = dx } = 
    try Env.find x renaming with Not_found -> assert false in
  { eq_desc = EQeq(floatpat dx, e); eq_loc = loc } :: eq_list

(** Translation of a pattern. Rename all names *)
let rec pattern renaming ({ p_desc = desc } as p) =
  let desc = match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> desc
    | Etuplepat(p_list) -> Etuplepat(List.map (pattern renaming) p_list)
    | Evarpat(n) -> 
        let { last_name = last_x } = Env.find n renaming in Evarpat(last_x) 
    | Erecordpat(label_pat_list) ->
        Erecordpat(List.map 
                      (fun (label, p) -> (label, pattern renaming p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraintpat(pattern renaming p, ty)
    | Ealiaspat(p1, n) -> 
        let { last_name = last_n} = Env.find n renaming in 
        Ealiaspat(pattern renaming p1, last_n)
    | Eorpat(p1, p2) ->
        Eorpat(pattern renaming p1, pattern renaming p2) in
  { p with p_desc = desc }

(** Expression from a pattern. Rename x into lx *)
let rec exp_of_pat renaming { p_desc = desc; p_loc = loc; p_typ = typ } =
  let desc = match desc with
    | Econstpat(i) -> Econst(i)
    | Econstr0pat(n) -> Econstr0(n)
    | Etuplepat(p_list) -> Etuple(List.map (exp_of_pat renaming) p_list)
    | Evarpat(n) -> 
        begin try let { in_name = lx } = Env.find n renaming in Elocal(lx) 
          with | Not_found -> assert false end
    | Erecordpat(label_pat_list) ->
        Erecord(List.map 
                   (fun (label, p) -> (label, exp_of_pat renaming p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraint(exp_of_pat renaming p, ty)
    | Ewildpat | Ealiaspat _ | Eorpat _ -> assert false in
  { e_desc = desc; e_loc = loc; e_typ = typ }

(* [last p] returns an expression equal to [p] with every variable [x] from [p] *)
(* is replaced by [last x] *)
let rec last { p_desc = desc; p_typ = ty; p_loc = loc } =
  let desc = match desc with
    | Econstpat(c) -> Econst(c)
    | Econstr0pat(c) -> Econstr0(c)
    | Etuplepat(p_list) -> Etuple(List.map last p_list)
    | Evarpat(n) -> Elast(n)
    | Erecordpat(label_pat_list) ->
        Erecord(List.map (fun (label, p) -> (label, last p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraint(last p, ty)
    | Ealiaspat _ | Eorpat _ | Ewildpat -> assert false in
  { e_desc = desc; e_typ = ty; e_loc = loc }

(** Translate an initialization [init x = e] for a continuous state variable [x] *)
(* Case 1:  next(pat) = true.  *)
(* [x = e0 -> if d then pre(next_x) else lx] *)
(* Case 2: current(pat) = true *)
(* [last_x = e0 -> if d then pre(x) else lx] *)
(* Case 3: neither of both is true *)
(* [x = e0 -> if d then pre(x) else lx  and last_x = x] *)
let translate_init renaming x e0 eq_list =
  let { in_name = in_name; last_name = last_name; next_name = next_name;
	is_set = is_set; is_next = is_next } =
    try Env.find x renaming with | Not_found -> assert false in
  match is_set, is_next with
    | false, false ->
        (* no definition of [x = ...] nor [next x = ...] *)
        (* [last_x = e0 -> if d then pre last_x else in_x] *)
        (eqmake (floatpat last_name) 
	  (minusgreater e0 (ifdiscrete (pre (floatvar last_name)) (floatvar in_name)))) :: 
	  eq_list
    | true, false ->
        (* [some definition of [x = ...] *)
	(* [last_x = e0 -> if d then pre x else in_x] *)
        (eqmake (floatpat last_name) 
	  (minusgreater e0 (ifdiscrete (pre (floatvar x)) (floatvar in_name)))) ::
	  eq_list
    | false, true ->
       (* [some definition of [next x = ...] *)
       (* [x = e0 -> if d then pre (next_name) else in_name] *)
      (eqmake (floatpat x)
	  (minusgreater e0 (ifdiscrete (pre (floatvar next_name)) (floatvar in_name)))) ::
	 eq_list
    | _ -> assert false
      
(** Translate a [next x = ...] where [x] is a continuous state variable *)
let translate_next renaming loc x e eq_list =
  let { in_name = l_name; next_name = next_name } =
    try Env.find x renaming with | Not_found -> assert false in
  { eq_desc = EQeq(floatpat next_name, e); eq_loc = loc } :: eq_list 

(** Translating an application. Do a special treatment for zero-crossing *)
(** operators. Leave other applications unchanged. *)
let app op e_list e_result =
  match op, e_list with
    | Einitial, [] -> 
        (* true -> false *) minusgreater ctrue cfalse
    | Edisc, [e] -> 
        (* if d then true -> pre x <> x else false *)
        ifdiscrete (minusgreater ctrue (boolop ("!=") [pre(e); e])) cfalse
    | Eon, [e1;e2] -> 
        (* e1 and e2 *)
        boolop "&&" [e1; e2]
    | op, e_list ->
        { e_result with e_desc = Eapp(op, e_list) }
    
(** Translation of discrete expressions *)
(* the only job is to replace [last x] by [last_x] when [x] appears in [renaming] *)
let rec expression renaming ({ e_desc = desc } as e) =
  match desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ -> e
    | Elast(x) ->
        begin try 
            let { last_name = last_x } = Env.find x renaming in 
            { e with e_desc = Elocal(last_x) } 
          with | Not_found -> e 
        end
    | Eapp(op, e_list) ->
        let e_list = List.map (expression renaming) e_list in
        app op e_list e
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (expression renaming) e_list) }
    | Erecord_access(e1, label) ->
        { e with e_desc = Erecord_access(expression renaming e1, label) }
    | Erecord(l_e_list) ->
        let l_e_list = 
          List.map (fun (label, e) -> (label, expression renaming e)) l_e_list in
        { e with e_desc = Erecord(l_e_list) }
    | Etypeconstraint(e1, ty) ->
        { e with e_desc = Etypeconstraint(expression renaming e1, ty) }
    | Elet(l, e1) ->
        (* as l has been normalized, no derivative is present inside *)
        let l = local renaming l in
        let e1 = expression renaming e1 in
        { e with e_desc = Elet(l, e1) }
    | Eseq(e1, e2) ->
        let e1 = expression renaming e1 in
        let e2 = expression renaming e2 in
        { e with e_desc = Eseq(e1, e2) }
    | Eperiod _ -> e
    | Epresent _ | Ematch _ -> assert false

(** Translation of discrete equations and locals. Only the substitution of *)
(** [last x] by [last_x] when it exists has to be done *)
and equation renaming eq =
  match eq.eq_desc with
    | EQeq(p, e) -> { eq with eq_desc = EQeq(p, expression renaming e) }
    | EQinit(p, e0, e_opt) -> 
        { eq with eq_desc = EQinit(p, expression renaming e0,
				   Misc.optional_map (expression renaming) e_opt) }
    | EQnext(p, e, e0_opt) -> 
        { eq with eq_desc = EQnext(p, expression renaming e,
				   Misc.optional_map (expression renaming) e0_opt) }
    | EQmatch(total, e, m_h_list) ->
        let e = expression renaming e in
        let m_h_list = 
          List.map 
            (fun ({ m_body = b } as m_h) -> { m_h with m_body = block renaming b }) 
            m_h_list in
        { eq with eq_desc = EQmatch(total, e, m_h_list) }
    | EQreset(b, e) -> 
        { eq with eq_desc = EQreset(block renaming b, expression renaming e) }
    | EQautomaton _ | EQpresent _ | EQder _ | EQemit _ -> assert false

and local renaming ({ l_eq = eq_list } as l) =
  { l with l_eq = List.map (equation renaming) eq_list }

and block renaming ({ b_locals = l_list; b_body = eq_list } as b) =
  { b with b_locals = List.map (local renaming) l_list; 
    b_body = List.map (equation renaming) eq_list }

(** Translation of continuous computations *)
(* [equation renaming ctx eq_list eq = ctx', eq_list'] translates an equation. *)
(* [renaming] is a renamming environment: [x -> dx + lx + last_x + nx] such that *)
(* every occurence of [der x] is replaced by [dx], [last x] by [last_x]. *)
(* The input state is [lx]. [nx = if d then x else dx] is added at the *)
(* definition point of [x] *)
(* [eq_list] is the already translated sequence of equations to which *)
(* the result is added *)
let rec equation renaming (ctx, eq_list) eq =
  match eq.eq_desc with
    | EQeq(p, { e_desc = Eapp(Eup, [e1]) }) ->
        let e1 = expression renaming e1 in
        let ctx, e1, extra_eq = up ctx e1 in
        let eq_e1 = { eq with eq_desc = EQeq(p, e1) } in
        ctx, eq_e1 :: extra_eq :: eq_list
    | EQeq(p, ({ e_desc = Eapp(Eop(f), e_list) } as e)) 
        when Types.is_a_hybrid_node f ->
        let e_list = List.map (expression renaming) e_list in
        (* introduction of special names to store internal states/zero-crossings *)
        let z   = Ident.fresh "z" in
        let upz = Ident.fresh "upz" in
        let lx  = Ident.fresh "lx" in
        let nx  = Ident.fresh "nx" in
          (* (upz, nx, p) = f(z, lx, d, e1,...,en) *)
        (* get the type for the input structure of zero-crossing and *)
        (* for continuous states *)
        let (ty_z, ty_lx), (ty_upz, ty_nx) = concrete_type eq.eq_loc f in
        let (p_nx,  ctx_out_x, v_lx, ctx_in_x) =
          if is_ty_unit ty_nx then (unitpat, ctx.ctx_out_x, cunit, ctx.ctx_in_x)
          else (varpat nx ty_nx, State.cons(nx, ty_nx) ctx.ctx_out_x,
                var lx ty_lx, State.cons(lx, ty_lx) ctx.ctx_in_x) in
        let (p_upz, ctx_upz, v_z, ctx_zero) =
          if is_ty_unit ty_upz then (unitpat, ctx.ctx_upz, cunit, ctx.ctx_zero)
          else (varpat upz ty_upz, State.cons(upz, ty_upz) ctx.ctx_upz,
                var z ty_z, State.cons(z, ty_z) ctx.ctx_zero) in
        let new_eq = 
          eqmake (tuplepat [p_upz; p_nx; p])
            { e with e_desc = 
                Eapp(Eop(f), v_z :: v_lx :: (boolvar discrete) :: e_list) } in
        { ctx_zero = ctx_zero;
          ctx_upz = ctx_upz;
          ctx_in_x = ctx_in_x;
          ctx_out_x = ctx_out_x; },
        new_eq :: eq_list
    | EQeq(p, e) ->
        let e = expression renaming e in
        ctx, { eq with eq_desc = EQeq(p, e) } :: eq_list
    | EQder(x, e, None, []) ->
        (* generate an equation: [dx = e] *)
        let e = expression renaming e in
        ctx, der renaming eq.eq_loc x e eq_list
    | EQinit({ p_desc = Evarpat(x) }, e0, None) when Env.mem x renaming ->
        (* a temporary solution for [init x = e] when [der x = ...] exists *)
        let e0 = expression renaming e0 in
        ctx, translate_init renaming x e0 eq_list
    | EQinit(pat, e0, e_opt) ->
        let e0 = expression renaming e0 in
        let e_opt = Misc.optional_map (expression renaming) e_opt in
        ctx, { eq with eq_desc = EQinit(pat, e0, e_opt) } :: eq_list
    | EQnext({ p_desc = Evarpat(x) }, e, None) when Env.mem x renaming ->
	(* a temporary solution for [init x = e] when [der x = ...] exists *)
        let e = expression renaming e in
        ctx, translate_next renaming eq.eq_loc x e eq_list
    | EQnext(pat, e, e0_opt) ->
        let e = expression renaming e in
        let e0_opt = Misc.optional_map (expression renaming) e0_opt in
	ctx, { eq with eq_desc = EQnext(pat, e, e0_opt) } :: eq_list
    | EQmatch(total, e, m_h_list) ->
        let e = expression renaming e in
        (* project to a list of blocks *)
        let b_list = List.map (fun { m_body = b } -> b) m_h_list in
        let ctx', b_list = exclusive_blocks renaming b_list in
        (* then rebuild the list handlers *)
        let m_h_list =
          List.map2 (fun m_h b -> { m_h with m_body = b }) m_h_list b_list in
        let new_eq = { eq with eq_desc = EQmatch(total, e, m_h_list) } in
        pair ctx ctx', new_eq :: eq_list
    | EQreset(b, e) ->
        let e = expression renaming e in
        let ctx_b, b = block renaming b in
        let new_eq = { eq with eq_desc = EQreset(b, e) } in
        pair ctx ctx_b, new_eq :: eq_list
    | EQemit _ | EQpresent _ | EQautomaton _ | EQder _ -> assert false

and equation_list renaming ctx eq_list = 
  List.fold_left (equation renaming) (ctx, []) eq_list
      
(* translate a list of exclusive blocks. no sharing is done for the moment *)
and exclusive_blocks renaming b_list =
  (* first translate each block in the list *)
  let ctx_b_list = List.map (block renaming) b_list in
  let ctx_list, b_list = List.split ctx_b_list in
  (* compute the whole set of extra input/output variables *)
  let ctx = merge ctx_list in
  (* complement every handler with a default value [dx_i = 0.0] *)
  let b_list = List.map2 (complement ctx) ctx_list b_list in
  ctx, b_list

and block renaming ({b_vars = n_list; b_body = eq_list; b_env = n_env} as b) =
  let renaming0, n_list, n_env = build_renaming n_list n_env in
  let renaming = Env.append renaming0 renaming in
  let ctx = ctx_of_renaming renaming0 in
  let ctx_eq_list, eq_list = equation_list renaming empty eq_list in
  let eq_list = add_equations_for_nx renaming0 eq_list in
  pair ctx ctx_eq_list, 
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }

and local renaming ({ l_eq = eq_list; l_env = l_env } as l) = 
  let renaming0, _, l_env = build_renaming [] l_env in
  let ctx = ctx_of_renaming renaming0 in
  (* [variables from [eq_list] are modified locally *)
  let renaming_eq_list = Env.append renaming0 renaming in
  let ctx_eq_list, eq_list = equation_list renaming_eq_list empty eq_list in
  let eq_list = add_equations_for_nx renaming0 eq_list in
  let l_env = env_of ctx_eq_list l_env in
  renaming,
  pair ctx ctx_eq_list, 
  { l with l_eq = eq_list; l_env = l_env }     

(** Adds extra inputs. [(ctx_zero.(1);...;ctx_zero.(n)),
                        (ctx_in_x.(1);...;ctx_in_x.(m))] and [discrete] *)
let inputs { ctx_zero = l_zero; ctx_in_x = l_lx } p_list =
  let l_zero = 
    State.fold (fun (id, ty) acc -> (varpat id ty) :: acc) l_zero [] in
  let zero = tuplepat l_zero in
  let l_lx = 
    State.fold (fun (id, ty) acc -> (varpat id ty) :: acc) l_lx [] in
  let lx = tuplepat l_lx in
  zero :: lx :: (boolpat discrete) :: p_list

(** Adds extra outputs. [(ctx_upz.(1);...;ctx_upz.(n)),
                        (ctx_out_x.(1);...;ctx_out_x.(m))] *)
let outputs { ctx_upz = l_upz; ctx_out_x = l_nx } e =
  let l_upz = State.fold (fun (id, ty) acc -> (var id ty) :: acc) l_upz [] in
  let upz = tuple l_upz in
  let l_nx = State.fold (fun (id, ty) acc -> (var id ty) :: acc) l_nx [] in
  let nx = tuple l_nx in
  tuple [upz; nx; e]

(** Translation of a normalized expression. *)
(** Once normalised, it is either of the form [e] with no more *)
(** lets inside or a [let L in e] *)
let rec nexpression e = 
  match e.e_desc with
    | Elet(l, e1) ->
        let _, ctx, l = local Env.empty l in
        ctx, { e with e_desc = Elet(l, outputs ctx e1) }
    | _ -> empty, outputs empty e

(** Store representative types for continuous states and zero-crossings in the
 ** module table. See concrete_type. *)
let set_cont_desc { ctx_in_x; ctx_upz } f =
  (* make a type for each of the components *)
  let typof l = 
    let l = State.fold (fun (id, ty) acc -> ty :: acc) l [] in
    match l with | [] -> Initial.typ_unit | [t] -> t | l -> Types.product l in

  Global.set_cont_desc (Modules.find_value (Lident.Name(f)))
    (Some (Global.Ctuple (typof ctx_in_x, typof ctx_upz)))

let implementation impl =
  match impl.desc with
    | Efundecl(f, ({ f_kind = C; f_args = p_list; f_body = e } as body)) ->
        (* add extra input. [e] is supposed to be normalized *)
        let ctx, e = nexpression e in
        (* modify the type of f in the symbol table *)
        set_cont_desc ctx f;
        (* final output *)
        let p_list = inputs ctx p_list in
        { impl with desc = 
            Efundecl(f, { body with f_kind = D; f_args = p_list; f_body = e }) }
    | _ -> impl
        
let implementation_list impl_list = Misc.iter implementation impl_list

