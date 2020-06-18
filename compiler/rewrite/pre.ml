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

(* Translation of fby/pre/next/up into init/last *)
(* After this pass equations are of the form: *)
(* eq ::= x = e | x = e | der x = e | x = up(e) | y = f(e) *)
(*              | init x = e *)
(*              | match e with P1 -> b1 | ... Pn -> bn *)
(*
    [e1 fby e2] => [let rec init x = e1 and x = e2 and r = last x in r]

    [pre(e)] => [let rec m = e and x = last m in x]

    [next x = e] => [nx = e], replace all occ. of [init x = e0]
                              by [init nx = e0 and add an equation
                              [x = last nx]

    [up(e)] => [let x = up(e) in x]

    [e1 -> e2] => [let x = e1 -> e2 in x]

    [horizon(e)] => [let x = horizon(e) in x]

    [f(e)] => let x = f(e) in x
*)

open Misc
open Location
open Deftypes
open Zelus
open Ident
open Zaux

(* Defines a value [let x = e in e_let] *)
let let_value e =
  let x = Ident.fresh "x" in
  let l_env = Env.singleton x (Deftypes.entry Sval e.e_typ) in
  Zaux.make_let l_env [Zaux.eq_make x e] (var x e.e_typ)

let let_value e =
  let x = Ident.fresh "x" in
  let l_env = Env.singleton x (Deftypes.entry Sval e.e_typ) in
  Zaux.make_let l_env [Zaux.eq_make x e] (var x e.e_typ)

(* Defines a state variable with initialization or not *)
(* [let init m = e0 and m = e and x = last m in x] *)
let let_last_value e0_opt e =
  let m = Ident.fresh "m" in
  let x = Ident.fresh "x" in
  let mem = Deftypes.previous Deftypes.empty_mem in
  let eq_list = [eq_make m e; eq_make x (last m e.e_typ)] in
  let mem, eq_list =
    match e0_opt with
    | None -> mem, eq_list
    | Some(e0) -> Deftypes.initialized mem, (eq_init m e0) :: eq_list in
  Zaux.make_let
    (Env.add x (Deftypes.entry Sval e.e_typ)
       (Env.singleton m (Deftypes.entry (Smem mem) e.e_typ))) eq_list
    (var x e.e_typ)

(* Define a zero-crossing *)
let let_zero_value e =
  let x = Ident.fresh "x" in
  let mem = Deftypes.zero Deftypes.empty_mem in
  let l_env = Env.singleton x (Deftypes.entry mem e.e_typ) in
  Zaux.make_let l_env [Zaux.eq_make x e] (var x e.e_typ)

(* Computes the set of variables defined by a "next". Change the *)
(* environment *)
let env subst b_env =
  let change x ({ t_typ = ty; t_sort = sort } as entry)
      (env, subst, x_lx_eq_list) =
    match sort with
    | Smem ({ m_next = Some(true) } as m) ->
        let nx = Ident.fresh "nx" in
        Env.add x { entry with t_sort = Sval }
          (Env.add nx { entry with t_sort =
                                     Smem { m with m_next = Some(false);
					           m_previous = true } } env),
      Env.add x nx subst, (eq_make x (last nx ty)) :: x_lx_eq_list
    | Sstatic | Sval | Svar _ | Smem _ ->
        Env.add x entry env, subst, x_lx_eq_list in
  Env.fold change b_env (Env.empty, subst, [])


(** Translation of expressions. *)
let rec exp e =
  match e.e_desc with
  | Elocal _ | Econst _ | Econstr0 _ | Eglobal _ | Elast _ -> e
  | Etuple(e_list) ->
     { e with e_desc = Etuple (List.map exp e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map exp e_list) }
  | Eop(Efby, [e1; e2]) ->
     let e1 = exp e1 in
     let e2 = exp e2 in
     (* translate into [let rec init m = e1 and m = e2 and x = last m in x] *)
     let_last_value (Some(e1)) e2
  | Eop(Eminusgreater | Einitial | Ehorizon as op, e_list) ->
     let e_list = List.map exp e_list in
     (* turns it into [let m = op(e1,...,en) in x] *)
     let_value { e with e_desc = Eop(op, e_list) }
  | Eop(Eifthenelse, [e1; e2; e3]) ->
     let e1 = exp e1 in
     let e2 = exp e2 in
     let e3 = exp e3 in
     (* if [e2] (and [e3]) is stateful, name the result *)
     { e with e_desc =
		Eop(Eifthenelse,
		    [e1; if Unsafe.exp e2 then let_value e2 else e2;
		     if Unsafe.exp e3 then let_value e3 else e3]) }
  | Eop(Eunarypre, [e1]) ->
     let e1 = exp e1 in
     (* turns it into [let rec m = e1 and x = last m in x] *)
     let_last_value None e1
  | Eop(Eup, [e1]) ->
     let e1 = exp e1 in
     (* turns it into [let x = up(e1) in x] *)
     let_zero_value { e with e_desc = Eop(Eup, [e1]) }
  | Eop(op, e_list) -> { e with e_desc = Eop(op, List.map exp e_list) }
  | Eapp(app, e_op, e_list) ->
     let e_op = exp e_op in
     let e_list = List.map exp e_list in
     { e with e_desc = Eapp(app, e_op, e_list) }
  | Erecord(label_e_list) ->
      let label_e_list =
        List.map (fun (l, e) -> (l, exp e)) label_e_list in
     { e with e_desc = Erecord(label_e_list) }
  | Erecord_access(e_record, longname) ->
     { e with e_desc = Erecord_access(exp e_record, longname) }
  | Erecord_with(e_record, label_e_list) ->
      let label_e_list =
        List.map (fun (l, e) -> (l, exp e)) label_e_list in
     { e with e_desc = Erecord_with(exp e_record, label_e_list) }
  | Etypeconstraint(e1, ty) ->
     { e with e_desc = Etypeconstraint(exp e1, ty) }
  | Elet(l, e) ->
     let l = local l in { e with e_desc = Elet(l, exp e) }
  | Eblock(b, e) ->
     let b = block Env.empty b in { e with e_desc = Eblock(b, exp e) }
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(exp e1, exp e2) }
  | Eperiod { p_phase = p1; p_period = p2 } ->
     { e with e_desc = Eperiod
                         { p_phase = Misc.optional_map exp p1; p_period = exp p2 } }
  | Epresent _ | Ematch _ -> assert false

(** Translation of equations. *)
and equation subst eq_list ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(p, e) ->
     { eq with eq_desc = EQeq(p, exp e) } :: eq_list
  | EQpluseq(x, e) ->
     { eq with eq_desc = EQpluseq(x, exp e) } :: eq_list
  | EQnext(x, e, None) ->
     let nx = try Env.find x subst with Not_found -> assert false in
     { eq with eq_desc = EQeq(varpat nx e.e_typ, exp e) } :: eq_list
  | EQnext(x, e, Some(e0)) ->
     let e = exp e in
     let e0 = exp e0 in
     let nx = try Env.find x subst with Not_found -> assert false in
     { eq with eq_desc = EQinit(nx, e0) } ::
       { eq with eq_desc = EQeq(varpat nx e.e_typ, e) } :: eq_list
  | EQinit(x, e0) ->
     let nx = try Env.find x subst with Not_found -> x in
     { eq with eq_desc = EQinit(nx, exp e0) } :: eq_list
  | EQmatch(total, e, p_h_list) ->
     let p_h_list =
       List.map (fun ({ m_body = b } as h) -> let b = block subst b in
					      { h with m_body = b })
		p_h_list in
     { eq with eq_desc = EQmatch(total, exp e, p_h_list) } :: eq_list
  | EQreset(res_eq_list, e) ->
     let res_eq_list = equation_list subst [] res_eq_list in
     { eq with eq_desc = EQreset(res_eq_list, exp e) } :: eq_list
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(equation_list subst [] and_eq_list) } :: eq_list
  | EQbefore(before_eq_list) ->
     { eq with eq_desc =
		 EQbefore(equation_list subst [] before_eq_list) } :: eq_list
  | EQder(x, e, None, []) ->
     let nx = try Env.find x subst with Not_found -> x in
     { eq with eq_desc = EQder(nx, exp e, None, []) } :: eq_list
  | EQblock(b) -> let b = block subst b in
		  { eq with eq_desc = EQblock(b) } :: eq_list
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
     let index ({ desc = desc } as ind) =
       let desc = match desc with
	 | Einput(x, e) -> Einput(x, exp e)
	 | Eoutput _ -> desc
	 | Eindex(x, e1, e2) ->
	    Eindex(x, exp e1, exp e2) in
       { ind with desc = desc } in
     let init ({ desc = desc } as ini) =
       let desc = match desc with
	 | Einit_last(x, e) -> Einit_last(x, exp e) in
       { ini with desc = desc } in
     let i_list = List.map index i_list in
     let init_list = List.map init init_list in
     let b_eq_list = block subst b_eq_list in
     { eq with eq_desc =
		 EQforall { body with for_index = i_list;
				      for_init = init_list;
				      for_body = b_eq_list } }
     :: eq_list
    | EQpresent _ | EQautomaton _ | EQder _ | EQemit _ -> assert false

and equation_list subst new_eq_list eq_list =
  List.fold_left (equation subst) new_eq_list eq_list

and block subst ({ b_locals = l_list; b_body = eq_list; b_env = b_env } as b) =
  (* Identify variables defined by a "next". Renames them and *)
  (* add a copy *)
  let b_env, subst, x_lx_eq_list = env subst b_env in
  let l_list = List.map local l_list in
  let eq_list = equation_list subst x_lx_eq_list eq_list in
  { b with b_locals = l_list; b_body = eq_list; b_env = b_env }

and local ({ l_eq = l_eq_list; l_env = l_env } as l) =
  let l_env, subst, x_lx_eq_list = env Env.empty l_env in
  let l_eq_list = equation_list subst x_lx_eq_list l_eq_list in
  { l with l_eq = l_eq_list; l_env = l_env }

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl(_, { f_kind = A }) -> impl
  | Efundecl(n, ({ f_body = e; f_env = f_env } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
