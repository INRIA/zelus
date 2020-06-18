(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Remove nested declaration of variables *)
(* Preserves the sequential order defined by a let/in *)
(* declaration and, thus, possible side effects in them *)
(* E.g., in [let x = e1 in e2], all side effects in [e1] are done before *)
(* those of [e2] *)
(* [let x = e1 in e2] has the behavior of [let x = e1 before y = e2 in y] *)

open Misc
open Location
open Ident
open Lident
open Deftypes
open Zelus
open Zaux

(* a structure to represent nested equations before they are turned into *)
(* valid Zelus equations *)
type ctx = { env: Deftypes.tentry Env.t State.t; eqs: eq State.t }

let empty = { env = State.empty; eqs = State.empty }
let par { env = env1; eqs = eqs1 } { env = env2; eqs = eqs2 } =
  { env = State.par env1 env2; eqs = State.par eqs1 eqs2 }
let seq { env = env1; eqs = eqs1 } { env = env2; eqs = eqs2 } =
  { env = State.seq env1 env2; eqs = State.seq eqs1 eqs2 }
let add eq ({ eqs = eqs } as ctx) =
  { ctx with eqs = State.par (State.singleton eq) eqs }
				   				      
let optional f e_opt =
  match e_opt with
    | None -> None, { env = State.Empty; eqs = State.Empty }
    | Some(e) -> let e, ctx = f e in Some(e), ctx

let par_fold f l =
  Misc.map_fold
    (fun { env = env; eqs = eqs } x ->
     let y, { env = env_y; eqs = eqs_y } = f x in
     y, { env = State.par env env_y; eqs = State.par eqs eqs_y })
    { env = State.Empty; eqs = State.Empty } l

(* translate a context [ctx] into an environment and an equation *)
let equations eqs =
  (* computes the set of sequential equations *)
  let rec seq eqs eq_list =
    match eqs with
    | State.Empty -> eq_list
    | State.Cons(eq, eqs) -> eq :: seq eqs eq_list
    | State.Seq(eqs1, eqs2) ->
       seq eqs1 (seq eqs2 eq_list)
    | State.Par(eqs1, eqs2) ->
       let par_eq_list = par [] eqs1 in
       let par_eq_list = par par_eq_list eqs2 in
       Zaux.par par_eq_list :: eq_list
  (* and the set of parallel equations *)
  and par eq_list eqs =
    match eqs with
    | State.Empty -> eq_list
    | State.Cons(eq, eqs) -> par (eq :: eq_list) eqs
    | State.Seq(eqs1, eqs2) ->
       let seq_eq_list = seq eqs2 [] in
       let seq_eq_list = seq eqs1 seq_eq_list in
       Zaux.before seq_eq_list :: eq_list
    | State.Par(eqs1, eqs2) ->
       par (par eq_list eqs1) eqs2 in
  par [] eqs

(* every variable from [ctx] becomes a local variable *)
let add_locals n_list l_env { env = env; eqs = eqs } =
  let eq_list = equations eqs in
  let l_env = State.fold (fun env acc -> Env.append env acc) env l_env in
  let n_list =
    State.fold (fun env acc ->
		Env.fold
		  (fun n entry acc -> (Zaux.vardec_from_entry n entry) :: acc)
		  env acc) env n_list in
  n_list, l_env, eq_list
				      
(** Translation of expressions *)
let rec expression ({ e_desc = desc } as e) =
  match desc with
  | Elocal _ | Eglobal _ | Econst _
  | Econstr0 _ | Elast _ -> e, empty
  | Eop(op, e_list) ->
     let e_list, ctx = par_fold expression e_list in
     { e with e_desc = Eop(op, e_list) }, ctx
  | Eapp(app, e_op, e_list) ->
     let e_op, ctx_e_op = expression e_op in
     let e_list, ctx = par_fold expression e_list in
     { e with e_desc = Eapp(app, e_op, e_list) },
     par ctx_e_op ctx
  | Etuple(e_list) ->
     let e_list, ctx = par_fold expression e_list in
     { e with e_desc = Etuple(e_list) }, ctx
  | Econstr1(c, e_list) ->
     let e_list, ctx = par_fold expression e_list in
     { e with e_desc = Econstr1(c, e_list) }, ctx
  | Erecord_access(e_record, l) ->
     let e_record, ctx = expression e_record in
     { e with e_desc = Erecord_access(e_record, l) }, ctx
  | Erecord(l_e_list) ->
     let l_e_list, ctx =
       par_fold
	 (fun (l, e) -> let e, ctx = expression e in (l, e), ctx) l_e_list in
     { e with e_desc = Erecord(l_e_list) }, ctx
  | Erecord_with(e_record, l_e_list) ->
     let e_record, ctx_record = expression e_record in
     let l_e_list, ctx =
       par_fold
	 (fun (l, e) -> let e, ctx = expression e in (l, e), ctx) l_e_list in
     { e with e_desc = Erecord_with(e_record, l_e_list) },
     par ctx_record ctx
  | Etypeconstraint(e1, ty) ->
     let e1, ctx = expression e1 in
     { e with e_desc = Etypeconstraint(e1, ty) }, ctx
  | Elet(l, e_let) ->
     let ctx = local l in
     let e_let, ctx_let = expression e_let in
     e_let, seq ctx ctx_let
  | Eblock({ b_locals = l_list; b_env = b_env; b_body = eq_list }, e) ->
     let l_ctx = local_list l_list in
     let eq_list_ctx = par_equation_list eq_list in
     let e, ctx_e = expression e in
     e, seq { empty with env = State.singleton b_env }
	    (seq l_ctx (seq eq_list_ctx ctx_e))
  | Eseq(e1, e2) ->
     (* [e1; e2] is a short-cut for [let _ = e1 in e2] *)
     let e1, ctx1 = expression e1 in
     let e2, ctx2 = expression e2 in
     let _e1 =
       Zaux.eqmake (EQeq({ Zaux.wildpat with p_typ = e1.e_typ }, e1)) in
     e2, seq ctx1 (seq { empty with eqs = State.singleton _e1 } ctx2)
  | Epresent _ | Ematch _ | Eperiod _ -> assert false
				    
(** Translate an equation. *)
and equation ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, e) ->
     let e, ctx = expression e in
     add { eq with eq_desc = EQeq(p, e) } ctx
  | EQpluseq(n, e) ->
     let e, ctx_e = expression e in
     add { eq with eq_desc = EQpluseq(n, e) } ctx_e
  | EQder(n, e, e0_opt, []) ->
     let e, ctx = expression e in
     let e0_opt, ctx0 = optional expression e0_opt in
     let eq = { eq with eq_desc = EQder(n, e, e0_opt, []) } in
     add eq (par ctx ctx0)
  | EQinit(n, e0) ->
     let e0, ctx_e0 = expression e0 in
     add { eq with eq_desc = EQinit(n, e0) } ctx_e0
  | EQmatch(total, e, p_h_list) ->
     let e, ctx_e = expression e in
     let p_h_list =
       List.map 
         (fun ({ m_body = b } as p_h) ->
          let b = block b in
          { p_h with m_body = b })
         p_h_list in
     add { eq with eq_desc = EQmatch(total, e, p_h_list) } ctx_e
  | EQreset(res_eq_list, e) -> 
     let e, ctx_e = expression e in
     let { env = env; eqs = eqs } = par_equation_list res_eq_list in
     let res_eq_list = equations eqs in
     par ctx_e (add { eq with eq_desc = EQreset(res_eq_list, e) }
	            { empty with env = env })
  | EQand(and_eq_list) -> par_equation_list and_eq_list
  | EQbefore(before_eq_list) ->
     seq_equation_list before_eq_list     
  | EQblock { b_locals = l_list; b_env = b_env; b_body = eq_list } ->
     let l_ctx = local_list l_list in
     let eq_list_ctx = par_equation_list eq_list in
     par (seq l_ctx eq_list_ctx) { empty with env = State.singleton b_env }
  | EQforall ({ for_index = ind_list; for_init = i_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       match desc with
       | Einput(x, e) ->
	  let e, ctx_e = expression e in
	  { ind with desc = Einput(x, e) }, ctx_e 
       | Eoutput _ -> ind, empty
       | Eindex(x, e1, e2) ->
	  let e1, ctx_e1 = expression e1 in
	  let e2, ctx_e2 = expression e2 in
	  { ind with desc = Eindex(x, e1, e2) }, par ctx_e1 ctx_e2 in
     let init ({ desc = desc } as i) =
       match desc with
       | Einit_last(x, e) ->
	  let e, ctx_e = expression e in
	  { i with desc = Einit_last(x, e) }, ctx_e in
     let ind_list, ind_ctx = par_fold index ind_list in
     let i_list, i_ctx = par_fold init i_list in
     let b_eq_list = block b_eq_list in
     add { eq with eq_desc =
		       EQforall { body with for_index = ind_list;
					    for_init = i_list;
					    for_body = b_eq_list } }
	  (par ind_ctx i_ctx)	  
  | EQder _ | EQautomaton _ | EQpresent _ | EQemit _ | EQnext _ -> assert false
							       
and par_equation_list eq_list =
  List.fold_left (fun acc eq -> par (equation eq) acc) empty eq_list

and seq_equation_list eq_list =
  List.fold_left (fun acc eq -> seq acc (equation eq)) empty eq_list

(** Translating a block *)
(* Once normalized, a block is of the form *)
(* local x1,..., xn in do eq1 and ... and eqn *)
and block ({ b_vars = n_list; b_locals = l_list;
	     b_body = eq_list; b_env = b_env } as b) =
  (* first translate local declarations *)
  let l_ctx = local_list l_list in
  (* then the set of equations *)
  let ctx = par_equation_list eq_list in
  let ctx = seq l_ctx ctx in
  (* all local variables from [l_ctx] and [ctx] are now *)
  (* declared in that block *)
  let n_list, b_env, eq_list = add_locals n_list b_env ctx in
  { b with b_vars = n_list; b_locals = []; b_body = eq_list; b_env = b_env }
    
and local { l_eq = eq_list; l_env = l_env } =
  let ctx = par_equation_list eq_list in
  seq { empty with env = State.singleton l_env } ctx
	     
and local_list = function
  | [] -> empty
  | l :: l_list -> 
     let l_ctx = local l in
     let ctx = local_list l_list in
     seq l_ctx ctx
	       
let implementation impl =
  let make_let e =
    let e, ctx = expression e in
    let _, env, eq_list = add_locals [] Env.empty ctx in
    Zaux.make_let env eq_list e in
  match impl.desc with
  | Eopen _ | Etypedecl _ -> impl
  | Econstdecl(n, is_static, e) ->
     { impl with desc = Econstdecl(n, is_static, make_let e) }
  | Efundecl(n, ({ f_kind = k; f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = make_let e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
