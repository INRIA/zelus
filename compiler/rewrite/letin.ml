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
(* Translate sequential lets into parallel ones *)
(* Preserves the order between side effects, i.e., if [e1] has *)
(* a side effect in [let x = e1 in e2], the order between [e1] and [e2] *)
(* is kept. This is done by adding extra data-dependences *)

open Misc
open Location
open Ident
open Lident
open Deftypes
open Zelus
open Zaux

(* a structure to represent nested equations before they are turned into *)
(* valid Zelus equations *)
type ctx = Deftypes.tentry Env.t * eq list

let make eq = Env.empty, [eq]
let extend l_env ctx = State.cons (l_env, []) ctx
				  
let optional f e_opt =
  match e_opt with
    | None -> None, State.Empty
    | Some(e) -> let e, ctx = f e in Some(e), ctx

let fold f l =
  List.fold_right
    (fun i (l, ctx) -> let i, ctx_i = f i in i :: l, State.par ctx_i ctx) l
    ([], State.empty)

let intro env e =
  let n = Ident.fresh "" in
  Env.add n { t_sort = Deftypes.value; t_typ = e.e_typ } env, eq_make n e, n

let after e w =
  if S.is_empty w then e
  else after_list
	 e (S.fold (fun n acc -> var n Deftypes.no_typ :: acc) w [])

(** Add one equation [n = e] to a handler *)
let add_equation n_e n m_h_list =
  let add ({ m_body = ({ b_body = eq_list;
			 b_write = ({ dv = dv } as w) } as b) } as m_h) =
    { m_h with m_body =
		 { b with b_body = n_e :: eq_list;
			  b_write = { w with dv = S.add n dv } } } in
  match m_h_list with [] -> [] | m_h :: m_h_list -> add m_h :: m_h_list
	 
(* express that [eq] depends on [w] if [eq] is unsafe. In that case *)
(* express that the equations that will follow [eq] depend on the variables *)
(* [w_p] written by [eq] *)
let rec do_after (env, eq_list, w) ({ eq_desc = desc } as eq) =
  if Unsafe.equation eq then
    match desc with
    | EQeq(p, e) ->
       let w_p = Vars.fv_pat S.empty S.empty p in
       if S.is_empty w_p then
	 (* a fresh equation is introduced and it depends on [w] *)
	 let env, n_e, n = intro env (after e w) in
	 env, n_e :: { eq with eq_desc = EQeq(p, var n e.e_typ) } :: eq_list,
	 S.singleton n
       else env, { eq with eq_desc = EQeq(p, after e w) } :: eq_list, w_p
    | EQpluseq(n, e) ->
       env, { eq with eq_desc = EQpluseq(n, after e w) } :: eq_list,
       S.singleton n
    | EQder(n, e, None, []) ->
       env, { eq with eq_desc = EQder(n, after e w, None, []) } :: eq_list,
       S.singleton n
    | EQinit(n, e) ->
       env, { eq with eq_desc = EQinit(n, after e w) } :: eq_list,
       S.singleton n
    | EQmatch(total, e, m_h_list) ->
       (* variables written by the [match/with] *)
       let w_p =
	 List.fold_left
	   (fun acc { m_body = { b_write = { dv = dv; di = di; der = der } } } ->
	    S.union acc (S.union dv (S.union di der))) S.empty m_h_list in
       if S.is_empty w_p then
	 (* a fresh equation is introduced inside a branch *)
	 let env, n_e, n = intro env (after Zaux.evoid w) in
	 let m_h_list = add_equation n_e n m_h_list in
	 env,
	 { eq with eq_desc = EQmatch(total, after e w, m_h_list) } :: eq_list,
	 S.singleton n
       else 
	 env,
	 { eq with eq_desc = EQmatch(total, after e w, m_h_list) } :: eq_list,
	 w_p
    | EQreset(res_eq_list, e) ->
       let env, res_eq_list, w_p =
	 List.fold_left do_after (env, [], w) res_eq_list in
       env, { eq with eq_desc = EQreset(res_eq_list, after e w) } :: eq_list, w_p
    | _ -> assert false
  else env, eq :: eq_list, w
			      
(* translate a context [ctx] into an environment and a list of equations *)
let env_eq_list_of_ctx ctx =
  (* [env] is an environment; [eq_list] a list of equations; [w] the *)
  (* set of write variables for unsafe computations in [eq_list] *)
  let rec equations (env, eq_list, w) ctx =
    match ctx with
    | State.Empty -> env, eq_list, w
    | State.Cons((env0, eq_list0), ctx) ->
       let env, eq_list, w = equations (Env.append env env0, eq_list, w) ctx in
       List.fold_left do_after (env, eq_list, w) eq_list0
    | State.Seq(ctx1, ctx2) ->
       equations (equations (env, eq_list, w) ctx1) ctx2
    | State.Par(ctx1, ctx2) ->
       let env, eq_list, w1 = equations (env, eq_list, w) ctx1 in
       let env, eq_list, w2 = equations (env, eq_list, w) ctx2 in
       env, eq_list, S.union w1 w2 in
  equations (Env.empty, [], S.empty) ctx
  
  
(* every variable from [ctx] becomes a local variable *)
let add_locals ctx n_list l_env =
  let env, eq_list, _ = env_eq_list_of_ctx ctx in
  let n_list =
    Env.fold
      (fun n entry n_list -> (Zaux.vardec_from_entry n entry) :: n_list)
      env n_list in
  let l_env = Env.append env l_env in
  n_list, l_env, eq_list


(** Translation of expressions *)
let rec expression ({ e_desc = desc } as e) =
  match desc with
  | Elocal _ | Eglobal _ | Econst _
  | Econstr0 _ | Elast _ -> e, State.empty
  | Eapp(op, e_list) ->
     let e_list, ctx = fold expression e_list in
     { e with e_desc = Eapp(op, e_list) }, ctx
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
     let ctx = local l in
     let e_let, ctx_let = expression e_let in
     e_let, State.seq ctx ctx_let
  | Eseq(e1, e2) ->
     (* [e1; e2] is a short-cut for [let x = e1 in e2 after x] *)
     let e1, ctx1 = expression e1 in
     let e2, ctx2 = expression e2 in
     let env, n_e1, n = intro Env.empty e1 in
     e2, State.seq (State.cons (env, [n_e1]) ctx1) ctx2
  | Epresent _ | Ematch _ | Eperiod _ -> assert false
				    
(** Translate an equation. *)
and equation ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, e) ->
     let e, ctx = expression e in
     State.cons (make { eq with eq_desc = EQeq(p, e) }) ctx
  | EQpluseq(n, e) ->
     let e, ctx_e = expression e in
     State.cons (make { eq with eq_desc = EQpluseq(n, e) }) ctx_e
  | EQder(n, e, e0_opt, []) ->
     let e, ctx = expression e in
     let e0_opt, ctx0 = optional expression e0_opt in
     let eq = { eq with eq_desc = EQder(n, e, e0_opt, []) } in
     State.cons (make eq) (State.par ctx ctx0)
  | EQinit(n, e0) ->
     let e0, ctx_e0 = expression e0 in
     State.cons (make { eq with eq_desc = EQinit(n, e0) }) ctx_e0
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
     let env, res_eq_list, _ = env_eq_list_of_ctx res_ctx in
     State.cons (env, [{ eq with eq_desc = EQreset(res_eq_list, e) }]) ctx_e
  | EQblock { b_locals = l_list; b_env = b_env; b_body = eq_list } ->
     let l_ctx = local_list l_list in
     let b_ctx = equation_list eq_list in
     State.seq l_ctx (extend b_env b_ctx)
  | EQder _ | EQautomaton _ | EQpresent _ | EQemit _ | EQnext _ -> assert false
							       
and equation_list eq_list =
  List.fold_left (fun acc eq -> State.par (equation eq) acc) State.empty eq_list
		 
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
  extend l_env ctx
	     
and local_list = function
  | [] -> State.empty
  | l :: l_list -> 
     let l_ctx = local l in
     let ctx = local_list l_list in
     State.seq l_ctx ctx
	       
let implementation impl =
  let make_let e =
    let e, ctx = expression e in
    let env, eq_list, w = env_eq_list_of_ctx ctx in
    Zaux.make_let env eq_list (after e w) in
  match impl.desc with
  | Eopen _ | Etypedecl _ -> impl
  | Econstdecl(n, e) -> { impl with desc = Econstdecl(n, make_let e) }
  | Efundecl(n, ({ f_kind = k; f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = make_let e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
