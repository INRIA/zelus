(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* Translation of fby/pre/next/up into init/last *)
(* After this pass equations are of the form: *)
(* eq ::= x = e | x = e | der x = e | x = up(e) *)
(*              | init x = e *)
(*              | match e with P1 -> b1 | ... Pn -> bn *)
(*
    [e1 fby e2] => [let init x = e1 and x = e2 in last x]

    [pre(e)] => [let x = e in last x]

    [next x = e] => [x = e] and replace all occ. of [x] by [last x]

    [up(e)] => [let x = up(e) in x]

    [e1 -> e2] => [let x = e1 -> e2 in x]

    [horizon(e)] => [let x = horizon(e) in x]
*)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

(* Defines a value [let x = e in e_let] *)
let let_value x e e_let =
  let l_env = Env.singleton x (Deftypes.entry Sval e.e_typ) in
  Zaux.make_let l_env [Zaux.eq_make x e] e_let

(* Defines a state variable [let x = e in e_let] *)
let let_state_value x e e0_opt e_let =
  let mem = Deftypes.previous Deftypes.empty_mem in
  let eq_list = [eq_make x e] in
  let mem, eq_list =
    match e0_opt with
    | None -> mem, eq_list
    | Some(e0) -> Deftypes.initialized mem, (eq_init x e0) :: eq_list in
  Zaux.make_let
    (Env.singleton x (Deftypes.entry (Smem mem) e.e_typ)) eq_list e_let

(* Define a zero-crossing *)
let let_zero_value x e e_let =
  let mem = Deftypes.zero Deftypes.empty_mem in
  let l_env = Env.singleton x (Deftypes.entry mem e.e_typ) in
  Zaux.make_let l_env [Zaux.eq_make x e] e_let

(* Computes the set of variables modified by a "next" from an environment *)
let env subst b_env =
  let change n ({ t_sort = sort } as entry) (env, subst) =
    match sort with
    | Smem ({ m_next = Some(true) } as m) -> 
      Env.add n { entry with t_sort = Smem { m with m_next = Some(false); 
						    m_previous = true } } env,
      S.add n subst
    | Sstatic | Sval | Svar _ | Smem _ -> Env.add n entry env, subst in
  Env.fold change b_env (Env.empty, subst)

(** Translation of expressions. Replaces [x] by [last x] for all variables *)
(* that appear in [subst] *)
let rec exp subst e = 
  match e.e_desc with
  | Elocal(x) -> if S.mem x subst then { e with e_desc = Elast(x) } else e
  | Econst _ | Econstr0 _ | Eglobal _ | Elast _ | Eperiod _ -> e
  | Etuple(e_list) ->
     { e with e_desc = Etuple (List.map (exp subst) e_list) }
  | Eop(Efby, [e1; e2]) ->
     let e1 = exp subst e1 in
     let e2 = exp subst e2 in
     (* turns it into [let init x = e1 and x = e2 in last x] *)
     let x = Ident.fresh "m" in
     let_state_value x e2 (Some(e1)) (last x e1.e_typ)
  | Eop(Eminusgreater | Einitial | Ehorizon as op, e_list) ->
     let e_list = List.map (exp subst) e_list in
     (* turns it into [let m = op(e1,...,en) in x] *)
     let x = Ident.fresh "m" in
     let_value x { e with e_desc = Eop(op, e_list) } (var x e.e_typ)
  | Eop(Eunarypre, [e1]) ->
     let e1 = exp subst e1 in
     (* turns it into [let x = e1 in last x] *)
     let x = Ident.fresh "m" in
     let_state_value x e1 None (last x e1.e_typ)
  | Eop(Eup, [e1]) ->
     let e1 = exp subst e1 in
     (* turns it into [let x = up(e1) in x] *)
     let x = Ident.fresh "m" in
     let_zero_value x { e with e_desc = Eop(Eup, [e1]) } (var x e.e_typ)
  | Eop(op, e_list) -> { e with e_desc = Eop(op, List.map (exp subst) e_list) }
  | Eapp(app, e_op, e_list) ->
     let e_op = exp subst e_op in
     let e_list = List.map (exp subst) e_list in
     { e with e_desc = Eapp(app, e_op, e_list) }
  | Erecord(label_e_list) ->
     let label_e_list = List.map (fun (l, e) -> (l, exp subst e)) label_e_list in
     { e with e_desc = Erecord(label_e_list) }
  | Erecord_access(e1, longname) ->
     { e with e_desc = Erecord_access(exp subst e1, longname) }
  | Etypeconstraint(e1, ty) ->
     { e with e_desc = Etypeconstraint(exp subst e1, ty) }
  | Elet(l, e) -> 
     let l, subst = local subst l in { e with e_desc = Elet(l, exp subst e) }
  | Eblock(b, e) -> 
     let b, subst = block subst b in { e with e_desc = Eblock(b, exp subst e) }
  | Eseq(e1, e2) -> 
     { e with e_desc = Eseq(exp subst e1, exp subst e2) }
  | Epresent _ | Ematch _ -> assert false
	
(** Translation of equations. *)
and equation subst eq_list ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(p, e) -> 
     { eq with eq_desc = EQeq(p, exp subst e) } :: eq_list
  | EQpluseq(x, e) -> 
     { eq with eq_desc = EQpluseq(x, exp subst e) } :: eq_list
  | EQnext(x, e, None) ->
     { eq with eq_desc = EQeq(varpat x e.e_typ, exp subst e) } :: eq_list
  | EQnext(x, e, Some(e0)) ->
     let e = exp subst e in
     let e0 = exp subst e0 in
     { eq with eq_desc = EQinit(x, e0) } :: 
       { eq with eq_desc = EQeq(varpat x e.e_typ, e) } :: eq_list
  | EQinit(x, e0) ->
     { eq with eq_desc = EQinit(x, exp subst e0) } :: eq_list
  | EQmatch(total, e, p_h_list) ->
     let p_h_list = 
       List.map (fun ({ m_body = b } as h) -> let b, _ = block subst b in
					      { h with m_body = b }) 
		p_h_list in
     { eq with eq_desc = EQmatch(total, exp subst e, p_h_list) } :: eq_list
  | EQreset(res_eq_list, e) ->
     let res_eq_list = equation_list subst res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, exp subst e) } :: eq_list
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list subst and_eq_list) } :: eq_list
  | EQbefore(before_eq_list) ->
     { eq with eq_desc =
		 EQbefore(equation_list subst before_eq_list) } :: eq_list
  | EQder(n, e, None, []) ->
     { eq with eq_desc = EQder(n, exp subst e, None, []) } :: eq_list
  | EQblock(b) -> let b, _ = block subst b in
		  { eq with eq_desc = EQblock(b) } :: eq_list
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(x, e) -> Einput(x, exp subst e)
	 | Eoutput _ -> desc
	 | Eindex(x, e1, e2) ->
	    Eindex(x, exp subst e1, exp subst e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, exp subst e)
	 | Einit_value(x, e, c_opt) ->
	    Einit_value(x, exp subst e, c_opt) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list, _ = block subst b_eq_list in
     { eq with eq_desc =
		 EQforall { body with for_index = i_list;
				      for_init = init_list;
				      for_body = b_eq_list } }
     :: eq_list
    | EQpresent _ | EQautomaton _ | EQder _ | EQemit _ -> assert false
							       
and equation_list subst eq_list = List.fold_left (equation subst) [] eq_list

and block subst ({ b_locals = l_list; b_body = eq_list; b_env = b_env } as b) =
  (* Identify which defined variable is modified by a "next". *)
  (* Change its status to *)
  (* become a "last" variable *)
  let b_env, subst = env subst b_env in
  let l_list, subst = 
    List.fold_left
      (fun (l_list, subst) l -> let l, subst = local subst l in l :: l_list, subst)
      ([], subst) l_list in
  let eq_list = equation_list subst eq_list in
  { b with b_locals = List.rev l_list; b_body = eq_list; b_env = b_env }, subst
  
and local subst ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_env, subst = env subst l_env in
  let l_eq_list = equation_list subst l_eq_list in
  { l with l_eq = l_eq_list; l_env = l_env }, subst

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl(_, { f_kind = A }) -> impl
  | Efundecl(n, ({ f_body = e; f_env = f_env } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp S.empty e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
