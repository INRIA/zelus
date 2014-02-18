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
(* Normalization of programs before elimination of ODEs. Un-nesting of lets *)
(* and naming of all stateful function applications *)
(* normalization of expressions into: *)
(* e ::= op(e,...,e) | let E in e | .. with E stateless *)
(* eq ::= p = f(e1,...,en) | p = e with e safe and combinatorial *)
(* block ::= local x1,...,xn in do eq1 and ... and eqk done *)

open Misc
open Location
open Ident
open Lident
open Deftypes
open Zelus

let make desc ty = { e_desc = desc; e_loc = no_location; e_typ = ty }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty }
let varpat id ty = pmake (Evarpat(id)) ty
let var id ty = make (Elocal(id)) ty
let eqmake id e = 
  { eq_desc = EQeq(varpat id e.e_typ, e); eq_loc = Location.no_location }
let localmake eq_list l_env = 
  { l_eq = eq_list; l_env = l_env; l_loc = Location.no_location }

type ctx =
    { ctx_env: tentry Env.t;
      ctx_eq: eq State.t }

let empty = { ctx_env = Env.empty; ctx_eq = State.empty }
let pair { ctx_env = env1; ctx_eq = eq1 } { ctx_env = env2; ctx_eq = eq2 } =
  { ctx_env = Env.append env1 env2; ctx_eq = State.pair eq1 eq2 }
let add eq ctx = { ctx with ctx_eq = State.cons eq ctx.ctx_eq }
let is_empty { ctx_env = env; ctx_eq = eq } = 
  (Env.is_empty env) && (State.is_empty eq)

let optional f e_opt =
  match e_opt with
    | None -> None, empty
    | Some(e) -> let e, ctx = f e in Some(e), ctx

let fold f l =
  List.fold_right
    (fun i (l, ctx) -> let i, ctx_i = f i in i :: l, pair ctx_i ctx) l ([], empty)

(* translate a context [ctx] into a list of equations *)
let eq_list_of_ctx { ctx_env = env; ctx_eq = eq_s } =
  env, State.fold (fun eq acc -> eq :: acc) eq_s []

(* every variable from [ctx] becomes a local variable *)
let add_locals ctx n_list l_env =
  let env, eq_list = eq_list_of_ctx ctx in
  let n_list =
    Env.fold (fun n _ n_list -> n :: n_list) env n_list in
  let l_env = Env.append env l_env in
  n_list, l_env, eq_list

(** Is-it an operation which must be named? *)
let must_be_named op =
  match op with
    | Eop(f) -> not (Types.is_a_safe_function f)
    | Efby | Eunarypre | Eminusgreater | Eup | Edisc | Einitial -> true
    | _ -> false    

(** Translation of expressions *)
let rec nexpression ({ e_desc = desc } as e) =
  let e, ctx = expression e in
  if is_empty ctx then e
  else
    let env, eq_list = eq_list_of_ctx ctx in
    { e with e_desc = Elet(localmake eq_list env, e) }

(** Translation of expressions *)
and expression ({ e_desc = desc } as e) =
  match desc with
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e, empty
    | Eapp(op, e_list) ->
        let e_list, ctx = fold expression e_list in
        if must_be_named op
	then
	  (* introduce a fresh equation *)
	  let result = Ident.fresh "result" in
	  var result e.e_typ,
	  { ctx_env = 
	      Env.add result { t_sort = Val; t_typ = e.e_typ } ctx.ctx_env;
	    ctx_eq = 
	      State.cons 
		(eqmake result { e with e_desc = Eapp(op, e_list) }) 
		ctx.ctx_eq }
	else { e with e_desc = Eapp(op, e_list) }, ctx
    | Eperiod(p) ->
        let result = Ident.fresh "result" in
        var result e.e_typ,
        { ctx_env = Env.singleton result { t_sort = Val; t_typ = e.e_typ };
          ctx_eq = State.singleton (eqmake result e) }
    | Etuple(e_list) ->
        let e_list, ctx = fold expression e_list in
        { e with e_desc = Etuple(e_list) }, ctx
    | Erecord_access(e1, l) ->
        let e1, ctx = expression e1 in
        { e with e_desc = Erecord_access(e1, l) }, ctx
    | Erecord(l_e_list) ->
        let l_e_list, ctx = 
          fold (fun (l, e) -> let e, ctx = expression e in (l, e), ctx) l_e_list in
        { e with e_desc = Erecord(l_e_list) }, ctx
    | Etypeconstraint(e1, ty) ->
        let e1, ctx = expression e1 in
        { e with e_desc = Etypeconstraint(e1, ty) }, ctx
    | Elet(l, e_let) ->
        let e_let, ctx_e = expression e_let in
        let ctx = local l ctx_e in
        e_let, ctx
    | Eseq(e1, e2) ->
        let e1, ctx1 = expression e1 in
        let e2, ctx2 = expression e2 in
        { e with e_desc = Eseq(e1, e2) }, pair ctx1 ctx2
    | Epresent _ | Ematch _ -> assert false

(* Translating an equation *)
(* [eq_list] is the current list of equations to which [eq] must be added *)
(* [ctx] is the current context. *)
and equation ({ eq_desc = desc } as eq) ctx =
  let ctx_eq, eq = match desc with 
    | EQeq(p, ({ e_desc = Eapp(op, e_list) } as app)) when must_be_named op ->
        let e_list, ctx = fold expression e_list in
        ctx, { eq with eq_desc = 
	            EQeq(p, { app with e_desc = Eapp(op, e_list) }) }
    | EQeq(p, { e_desc = Eperiod _ }) -> empty, eq
    | EQder(n, e, e0_opt, []) ->
        let e, ctx_e = expression e in
        let e0_opt, ctx_e0 = optional expression e0_opt in
	let eq = { eq with eq_desc = EQder(n, e, e0_opt, []) } in
        pair ctx_e ctx_e0, eq
    | EQeq(p, e) -> 
        let e, ctx_e = expression e in
        ctx_e, { eq with eq_desc = EQeq(p, e) }
    | EQinit(p, e0, e_opt) -> 
        let e0, ctx_e0 = expression e0 in
        let e_opt, ctx_e = optional expression e_opt in
	pair ctx_e0 ctx_e, { eq with eq_desc = EQinit(p, e0, e_opt) }
    | EQnext(p, e, e0_opt) ->
        let e, ctx_e = expression e in
	let e0_opt, ctx_e0 = optional expression e0_opt in
	pair ctx_e ctx_e0, { eq with eq_desc = EQnext(p, e, e0_opt) }
    | EQemit(s, e_opt) -> 
        let e_opt, ctx_e = optional expression e_opt in
        ctx_e, { eq with eq_desc = EQemit(s, e_opt) }
    | EQmatch(total, e, p_h_list) ->
        let e, ctx_e = expression e in
        let p_h_list =
          List.map 
            (fun ({ m_body = b } as p_h) -> 
              let b = block b in
              { p_h with m_body = b })
            p_h_list in
        ctx_e, { eq with eq_desc = EQmatch(total, e, p_h_list) }
    | EQpresent(p_h_list, b_opt) ->
        let do_handler ({ p_cond = se; p_body = b } as p_h) (p_h_list, ctx) =
          let se, ctx_se = scond se in
          let b = block b in
          { p_h with p_cond = se; p_body = b } :: p_h_list, pair ctx ctx_se in
        
        let p_h_list, ctx_p_h = List.fold_right do_handler p_h_list ([], empty) in
        let b_opt = Misc.optional_map block b_opt in
        ctx_p_h, { eq with eq_desc = EQpresent(p_h_list, b_opt) }
    | EQautomaton(state_handler_list, se_opt) ->
        let do_handler ({ s_body = b } as a_h) = { a_h with s_body = block b } in
        empty, 
	{ eq with eq_desc = 
	    EQautomaton(List.map do_handler state_handler_list, se_opt) }  
    | EQreset(b, e) -> 
        let e, ctx_e = expression e in
        let b = block b in
        ctx_e, { eq with eq_desc = EQreset(b, e) }
    | EQder _ -> assert false in
  pair ctx_eq (add eq ctx)

and equation_list eq_list ctx = List.fold_right equation eq_list ctx

(** Translating a signal pattern *)
and scond ({ desc = desc } as sc ) =
  match desc with
  | Econdand(se1, se2) ->
      let se1, ctx1 = scond se1 in
      let se2, ctx2 = scond se2 in
      { sc with desc = Econdand(se1, se2) }, pair ctx1 ctx2
  | Econdor(se1, se2) ->
      let se1, ctx1 = scond se1 in
      let se2, ctx2 = scond se2 in
      { sc with desc = Econdor(se1, se2) }, pair ctx1 ctx2
  | Econdexp(e) ->
      let e, ctx = expression e in
      { sc with desc = Econdexp e }, ctx
  | Econdon(se1, e) ->
      let se1, ctx1 = scond se1 in
      let e, ctx = expression e in
      { sc with desc = Econdon(se1, e) }, pair ctx1 ctx
  | Econdpat(e, p) ->
      let e, ctx = expression e in
      { sc with desc = Econdpat(e, p) }, ctx

(** Translating a block *)
(* Once normalized, a block is of the form *)
(* local x1,..., xn in do eq1 and ... and eqn *)
and block 
    ({ b_vars = n_list; b_locals = l_list; b_body = eq_list; b_env = b_env } as b) =
  (* first translation the set of equations *)
  let ctx = equation_list eq_list empty in
  (* then every local declaration *)
  let ctx = List.fold_right local l_list ctx in
  (* every variable from ctx is now a local variable of the block *)
  let n_list, b_env, eq_list = add_locals ctx n_list b_env in
  { b with b_vars = n_list; b_locals = []; b_body = eq_list; b_env = b_env }

and local { l_eq = eq_list; l_env = l_env } ctx =
  let ctx = equation_list eq_list ctx in
  { ctx with ctx_env = Env.append l_env ctx.ctx_env }

let implementation only_hybrid impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_kind = k; f_body = e } as body)) ->
          let e = 
	    if only_hybrid then if k = C then nexpression e else e 
	    else nexpression e in
	  { impl with desc = Efundecl(n, { body with f_body = e }) }

let implementation_list only_hybrid impl_list = 
  Misc.iter (implementation only_hybrid) impl_list
