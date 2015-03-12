(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* Translate sequential lets into parallel ones with added names *)
(* to express precedence informations *)
(* Blocks are simplified *)
(* After this pass, expressions and equations are of the following form *)
(* eq ::= p = f(e1,...,en) | p = e | p = op(e) | p = up(e) | p = disc(e) *)
(*     | next x = e | init x = e | reset eq list every x *)
(* an equation [eq] is possibly associated to two sets of names: *)
(* eq before {x1,..., xn} after {y1,..., yk} *)
(* means that [eq] must be done before {x1,...,xn} are red; after {y1,...,yk} *)
(* are set *)
(* expression [e] is now stateless *)
(* block ::= local x1,...,xn in do eq1 and ... and eqk done *)

open Misc
open Location
open Ident
open Lident
open Deftypes
open Zelus

let make desc ty =
  { e_desc = desc; e_typ = ty; e_loc = Location.no_location; e_caus = [] }
let pmake desc ty =
  { p_desc = desc; p_loc = no_location; p_typ = ty; p_caus = [] }
let varpat id ty = pmake (Evarpat(id)) ty
let var id ty = make (Elocal(id)) ty
let eqmake id e = 
  { eq_desc = EQeq(varpat id e.e_typ, e); eq_loc = Location.no_location;
    eq_before = S.empty; eq_after = S.empty; eq_write = Deftypes.empty }
let aftereq eq before after = 
  { eq with eq_before = before; eq_after = after }
let eqwildpat e = 
  { eq_desc = EQeq(pmake Ewildpat e.e_typ, e); eq_loc = Location.no_location;
    eq_before = S.empty; eq_after = S.empty; eq_write = Deftypes.empty }
let localmake eq_list l_env = 
  { l_eq = eq_list; l_env = l_env; l_loc = Location.no_location }

(* an environment and equation *)
type ctx = (tentry Env.t * eq list) State.t

let make eq = Env.empty, [eq]

let optional f e_opt =
  match e_opt with
    | None -> None, State.empty
    | Some(e) -> let e, ctx = f e in Some(e), ctx

let fold f l =
  List.fold_right
    (fun i (l, ctx) -> let i, ctx_i = f i in i :: l, State.par ctx_i ctx) l
    ([], State.empty)

(* applications of a stateful function must be named *)
let named = function
  | Eop(_, f) when not (Types.is_a_function f) -> true
  | Eup | Edisc | Einitial | Efby | Eunarypre | Eminusgreater -> true
  | _ -> false


(** An expression or equation is unsafe if it contains an unsafe operation. *)
let rec unsafe { e_desc = desc } =
    match desc with
    | Eapp(Eop(_, f), _) when not (Types.is_a_safe_function f) -> true
    | Etuple(e_list) | Eapp(_, e_list) -> List.exists unsafe e_list
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> unsafe e
    | Erecord(f_e_list) ->
       List.exists (fun (_, e) -> unsafe e) f_e_list
    | Eseq(e1, e2) -> (unsafe e1) || (unsafe e2)
    | Elocal _ | Elast _ | Econst _ | Econstr0 _ 
    | Eglobal _ | Eperiod _ -> false
    | Elet _ -> true
    | Epresent _ | Ematch _ -> assert false

let unsafe_eq { eq_desc = desc } =
  match desc with
  | EQeq(_, e) -> unsafe e
  | _ -> true

(* translate a context [ctx] into a list of equations *)
let env_eq_list_of_ctx ctx =
  let par after1 after2 = S.union after1 after2 in
  let seq before after = if S.is_empty after then before else after in

  (* translate one equation *)
  let equation before (eq_list, after) eq =
    if unsafe_eq eq then
      let after_eq = S.singleton (Ident.fresh "o") in
      (* Warning: before and after are inversed on purpose! [before] is *)
      (* the set of names that must be computed before [eq] *)
      (* after is the set of names modified by [eq] *)
      aftereq eq after_eq before :: eq_list, par after after_eq
    else eq :: eq_list, after in

  let rec flat before ((env_acc, eq_list_acc) as acc) ctx =
    match ctx with
    | State.Empty -> acc, S.empty
    | State.Cons((env, eq_list), ctx) ->
       let env_acc = Env.append env env_acc in
       let eq_list_acc, after_acc =
	 List.fold_left (equation before) (eq_list_acc, S.empty) eq_list in
       let acc, after = flat before (env_acc, eq_list_acc) ctx in
       acc, par after_acc after
    | State.Par(ctx1, ctx2) ->
       let acc, after1 = flat before acc ctx1 in
       let acc, after2 = flat before acc ctx2 in
       acc, par after1 after2
    | State.Seq(ctx1, ctx2) ->
       let acc, after = flat before acc ctx1 in
       let acc, after = flat (seq before after) acc ctx2 in
       acc, seq before after in
  let (env, eq_list), _ = flat S.empty (Env.empty, []) ctx in
  env, eq_list

(* every variable from [ctx] becomes a local variable *)
let add_locals ctx n_list l_env =
  let env, eq_list = env_eq_list_of_ctx ctx in
  let n_list =
    Env.fold (fun n _ n_list -> n :: n_list) env n_list in
  let l_env = Env.append env l_env in
  n_list, l_env, eq_list


(** Translation of expressions *)
let rec nexpression ({ e_desc = desc } as e) =
  let e, ctx = expression e in
  if State.is_empty ctx then e
  else
    let env, eq_list = env_eq_list_of_ctx ctx in
    { e with e_desc = Elet(localmake eq_list env, e) }
      
(** Translation of expressions *)
and expression ({ e_desc = desc } as e) =
  match desc with
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e, State.empty
  | Eapp(op, e_list) ->
     let e_list, ctx = fold expression e_list in
     let e = { e with e_desc = Eapp(op, e_list) } in
     if named op then
       (* introduce a fresh equation. *)
       let result = Ident.fresh "result" in
       let eq = eqmake result e in
       var result e.e_typ,
       State.cons
	 (Env.singleton result { t_sort = Val; t_typ = e.e_typ }, [eq]) ctx
     else e, ctx
  | Eperiod(p) ->
     let result = Ident.fresh "result" in
     var result e.e_typ,
     State.singleton (Env.singleton result { t_sort = Val; t_typ = e.e_typ },
		      [eqmake result e])
  | Etuple(e_list) ->
     let e_list, ctx = fold expression e_list in
     { e with e_desc = Etuple(e_list) }, ctx
  | Erecord_access(e1, l) ->
     let e1, ctx = expression e1 in
     { e with e_desc = Erecord_access(e1, l) }, ctx
  | Erecord(l_e_list) ->
     let l_e_list, ctx = 
       fold (fun (l, e) -> 
	     let e, ctx = expression e in (l, e), ctx) l_e_list in
     { e with e_desc = Erecord(l_e_list) }, ctx
  | Etypeconstraint(e1, ty) ->
     let e1, ctx = expression e1 in
     { e with e_desc = Etypeconstraint(e1, ty) }, ctx
  | Elet(l, e_let) ->
     let ctx = local l in
     let e_let, ctx_e = expression e_let in
     e_let, State.seq ctx ctx_e
  | Eseq(e1, e2) ->
     (* [e1; e2] is a short-cut for [let _ = e1 in e2] *)
     let ctx1 = expression_into_wildpat e1 in
     let e2, ctx2 = expression e2 in
     e2, State.seq ctx1 ctx2
  | Epresent _ | Ematch _ -> assert false
				    
and expression_into_wildpat e =
  let e, ctx = expression e in
  let eq = eqwildpat e in
  State.cons (Env.empty, [eq]) ctx
	     
and equation ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, { e_desc = Eperiod _ }) -> State.singleton (make eq)
  | EQeq(p, e) ->
     let e, ctx = expression e in
     State.cons (make { eq with eq_desc = EQeq(p, e) }) ctx
  | EQder(n, e, e0_opt, []) ->
     let e, ctx_e = expression e in
     let e0_opt, ctx_e0 = optional expression e0_opt in
     let eq = { eq with eq_desc = EQder(n, e, e0_opt, []) } in
     State.cons (make eq) (State.par ctx_e ctx_e0)
  | EQinit(n, e0) ->
     let e0, ctx_e0 = expression e0 in
     State.cons (make { eq with eq_desc = EQinit(n, e0) }) ctx_e0
  | EQset(ln, e) ->
     let e, ctx_e = expression e in
     State.cons (make { eq with eq_desc = EQset(ln, e) }) ctx_e
  | EQnext(n, e, e0_opt) ->
     let e, ctx_e = expression e in
     let e0_opt, ctx_e0 = optional expression e0_opt in
     State.cons (make { eq with eq_desc = EQnext(n, e, e0_opt) })
		(State.par ctx_e ctx_e0)
  | EQmatch(total, e, p_h_list) ->
     let e, ctx_e = expression e in
     let p_h_list =
       List.map 
         (fun ({ m_body = b } as p_h) ->
          let b = block b in
          { p_h with m_body = b })
         p_h_list in
     State.cons (make { eq with eq_desc = EQmatch(total, e, p_h_list) }) ctx_e
  | EQreset(res_eq_list, e) -> 
     let e, ctx_e = expression e in
     let res_ctx = equation_list res_eq_list in
     let env, res_eq_list = env_eq_list_of_ctx res_ctx in
     State.cons (env, [{ eq with eq_desc = EQreset(res_eq_list, e) }]) ctx_e
  | EQblock { b_locals = l_list; b_env = b_env; b_body = eq_list } ->
     (* nested blocks are eliminated *)
     let l_ctx = local_list l_list in
     (* then the set of equations *)
     let b_ctx = equation_list eq_list in
     let b_ctx = State.seq l_ctx b_ctx in
     State.cons (b_env, []) b_ctx
  | EQder _ | EQautomaton _ | EQpresent _ | EQemit _ -> assert false

and equation_list eq_list =
  List.fold_left (fun acc eq -> State.par (equation eq) acc) State.empty eq_list
		 

(** Translating a signal pattern. *)
and scond ({ desc = desc } as sc ) =
  match desc with
  | Econdand(se1, se2) ->
      let se1, ctx1 = scond se1 in
      let se2, ctx2 = scond se2 in
      { sc with desc = Econdand(se1, se2) }, State.par ctx1 ctx2
  | Econdor(se1, se2) ->
      let se1, ctx1 = scond se1 in
      let se2, ctx2 = scond se2 in
      { sc with desc = Econdor(se1, se2) }, State.par ctx1 ctx2
  | Econdexp(e) ->
      let e, ctx = expression e in
      { sc with desc = Econdexp e }, ctx
  | Econdon(se1, e) ->
      let se1, ctx1 = scond se1 in
      let e, ctx = expression e in
      { sc with desc = Econdon(se1, e) }, State.par ctx1 ctx
  | Econdpat(e, p) ->
      let e, ctx = expression e in
      { sc with desc = Econdpat(e, p) }, ctx

(** Translating a block *)
(* Once normalized, a block is of the form *)
(* local x1,..., xn in do eq1 and ... and eqn *)
and block ({ b_vars = n_list; b_locals = l_list;
	     b_body = eq_list; b_env = b_env } as b) =
  (* first translate local declarations *)
  let l_ctx = local_list l_list in
  (* then the set of equations *)
  let ctx = equation_list eq_list in
  let ctx = State.seq l_ctx ctx in
  (* every variable from ctx is now a local variable of the block *)
  let n_list, b_env, eq_list = add_locals ctx n_list b_env in
  { b with b_vars = n_list; b_locals = []; b_body = eq_list; b_env = b_env }

and local { l_eq = eq_list; l_env = l_env } =
  let ctx = equation_list eq_list in
  State.cons (l_env, []) ctx

and local_list = function
  | [] -> State.empty
  | l :: l_list -> 
      let l_ctx = local l in
      let ctx = local_list l_list in
      State.seq l_ctx ctx

let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_kind = k; f_body = e } as body)) ->
         { impl with desc = Efundecl(n, { body with f_body = nexpression e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
