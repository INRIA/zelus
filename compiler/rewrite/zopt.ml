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

(* sharing of zero-crossings *)
(* Zero-crossing that appear in exclusive control branches are shared *)
(* This transformation is applied to normalized equations and expressions *)
(* [z1 = up(e1) # z2 = up(e2)] becomes [z1 = up(e1) # z1 = up(e2)] *)
(* Two phases algorithm: 
 * one phase computes zero-crossing variables and a substitution;
 * the second one applies the subsitution *)
open Ident
open Zelus
open Deftypes

(* an environment { env, size, subst }
 * env: the environment of zero-crossings;
 * ren: Ident.t -> Ident.t defines the renaming of zero-crossings
 * size: number of entries in env *)
type zenv = { env: Deftypes.tentry Env.t; ren: Ident.t Env.t; size: int }

let zempty = { env = Env.empty; ren = Env.empty; size = 0 }

(* Partition an environment into an environment of zero-crossing variables *)
(* and its complement *)
let zero_from_env env =
  let select key { t_sort = s } =
    match s with
    | Smem { m_kind = Some(Zero) } -> true | _ -> false in
  Env.partition select env

let vars_of_env vars env =
  List.filter (fun { vardec_name = x } -> Env.mem x env) vars
	      
(* Make a renaming from two environment *)
(* [make env2 env1 = ren] where 
 * ren = [x1\y1,..., xn\yn] with [x1,...,xn] = Dom(env2) 
 * and [y1,...,yn] in Dom(env1) *)
let make env2 env1 =
  (* [one key entry (l, acc) = acc + [key \ key'], l']
   * renames key into key' if [l = [key', entry'].l'] *)
  let one key _ (l, acc) =
    match l with
    | [] -> assert false (* env1 is supposed to be bigger than env2 *)
    | (key', _) :: l -> l, Env.add key key' acc in
  let l1 = Env.bindings env1 in
  let _, ren = Env.fold one env2 (l1, Env.empty) in
  ren

(* Compose two renamings. *)
(* [compose r2_by_1 r2 = r] returns an environment [r] such that:
 * r(x) = r2_by_1 (r2(x)) *)
let compose r2_by_1 r2 =
  Env.map (fun n2 -> try Env.find n2 r2_by_1 with Not_found -> assert false) r2
	  
(* Composition of two environment *)
let parallel
      { env = env1; ren = r1; size = s1 } { env = env2; ren = r2; size = s2 } =
  { env = Env.append env1 env2; ren = Env.append r1 r2; size = s1 + s2 }

let sharp
      { env = env1; ren = r1; size = s1 } { env = env2; ren = r2; size = s2 } =
  (* all names of env2 are renamed by those from env1 if s1 >= s2 *)
    if s1 >= s2
  then let r2_by_1 = make env2 env1 in
       let r = Env.append r1 (Env.append r2_by_1 (compose r2_by_1 r2)) in
       { env = env1; ren = r; size = s1 }
  else let r1_by_2 = make env1 env2 in
       let r = Env.append r2 (Env.append r1_by_2 (compose r1_by_2 r1)) in
       { env = env2; ren = r; size = s2 }
  
(* [equation eq = eq', zenv] where
 * eq': the new equation in which zero-crossing variables have been removed
 * zenv.env: the set of zero-crossing variables defined in eq
 * zenv.rename: Ident.t -> Ident.t, the substitution of zero-crossing variables *)
let rec equation ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq _ | EQpluseq _ | EQder _ | EQinit _ -> eq, zempty
  | EQmatch(total, e, m_h_list) ->
     let m_h_list, zenv =
       Misc.map_fold (fun acc ({ m_body = b } as m_h) ->
		      let b, zenv = block b in
		      { m_h with m_body = b },
		      sharp acc zenv)
		     zempty m_h_list in
     { eq with eq_desc = EQmatch(total, e, m_h_list) }, zenv
  | EQreset(eq_list, e) ->
     let eq_list, zenv = equation_list eq_list in
     { eq with eq_desc = EQreset(eq_list, e) }, zenv
  | EQand(and_eq_list) ->
     let and_eq_list, zenv = equation_list and_eq_list in
     { eq with eq_desc = EQand(and_eq_list) }, zenv
  | EQbefore(before_eq_list) ->
     let before_eq_list, zenv = equation_list before_eq_list in
     { eq with eq_desc = EQbefore(before_eq_list) }, zenv
  | EQforall _ -> eq, zempty
  | EQblock _ | EQpresent _ | EQautomaton _ | EQnext _ | EQemit _ ->
							  assert false

and equation_list eq_list = 
  Misc.map_fold (fun acc eq -> let eq, zenv = equation eq in
			       eq, parallel acc zenv)
		zempty eq_list

and block ({ b_vars = vars; b_env = b_env; b_body = eq_list } as b) =
  let zero_env, b_env = zero_from_env b_env in
  let eq_list, zenv = equation_list eq_list in
  { b with b_vars = vars_of_env vars b_env; b_env = b_env; b_body = eq_list },
  parallel { env = zero_env; ren = Env.empty; size = Env.cardinal zero_env } zenv

(* renaming *)
let rec rename_expression ren ({ e_desc = desc } as e) =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e
  | Elocal(x) -> { e with e_desc = Elocal(apply x ren) }
  | Elast(x) -> { e with e_desc = Elast(apply x ren) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (rename_expression ren) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (rename_expression ren) e_list) }
  | Erecord(n_e_list) -> 
     { e with e_desc =
		Erecord(List.map (fun (ln, e) ->
				  (ln, rename_expression ren e)) n_e_list) }
  | Erecord_access(e_record, ln) ->
     { e with e_desc = Erecord_access(rename_expression ren e_record, ln) }
  | Erecord_with(e_record, n_e_list) -> 
     { e with e_desc =
		Erecord_with(rename_expression ren e_record,
			     List.map
			       (fun (ln, e) ->
				(ln, rename_expression ren e)) n_e_list) }
  | Eop(op, e_list) ->
     { e with e_desc = Eop(op, List.map (rename_expression ren) e_list) }
  | Eapp(app, e_op, e_list) ->
     let e_op = rename_expression ren e_op in
     let e_list = List.map (rename_expression ren) e_list in
     { e with e_desc = Eapp(app, e_op, e_list) }
  | Etypeconstraint(e1, ty) -> 
     { e with e_desc = Etypeconstraint(rename_expression ren e1, ty) }      
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(rename_expression ren e1, rename_expression ren e2) }
  | Eperiod _ | Epresent _ | Ematch _ | Elet _ | Eblock _ -> assert false
						
and rename_local ren ({ l_eq = eq_list } as l) =
  let eq_list = rename_equation_list ren eq_list in
 { l with l_eq = eq_list }

and rename_equation ren ({ eq_desc = desc } as eq) =
  let desc = match desc with
    (* zero-crossing definitions must be of the form [x = up(e)] *)
    | EQeq({ p_desc = Evarpat(x) } as p, e) ->
       EQeq( { p with p_desc = Evarpat(apply x ren) }, rename_expression ren e)
    | EQeq(p, e) -> EQeq(p, rename_expression ren e)
    | EQpluseq(x, e) ->  EQpluseq(apply x ren, rename_expression ren e)
    | EQinit(x, e0) -> EQinit(apply x ren, rename_expression ren e0)
    | EQmatch(total, e, m_h_list) ->
       let m_h_list =
	 List.map
	   (fun ({ m_body = b } as m_h) ->
	    { m_h with m_body = rename_block ren b })
	   m_h_list in
       EQmatch(total, rename_expression ren e, m_h_list)
    | EQder(x, e, None, []) -> EQder(x, rename_expression ren e, None, [])
    | EQreset(res_eq_list, e) ->
       let e = rename_expression ren e in
       let res_eq_list = rename_equation_list ren res_eq_list in
       EQreset(res_eq_list, e)
    | EQand(and_eq_list) ->
       EQand(rename_equation_list ren and_eq_list)
    | EQbefore(before_eq_list) ->
       EQbefore(rename_equation_list ren before_eq_list)
    | EQforall ({ for_index = i_list; for_init = init_list;
		  for_body = b_eq_list } as body) ->
       let index ({ desc = desc } as ind) =
	 let desc = match desc with
	   | Einput(x, e) -> Einput(x, rename_expression ren e)
	   | Eoutput _ -> desc
	   | Eindex(x, e1, e2) -> Eindex(x, rename_expression ren e1,
					 rename_expression ren e2) in
	 { ind with desc = desc } in
       let init ({ desc = desc } as ini) =
	 let desc = match desc with
	   | Einit_last(x, e) -> Einit_last(x, rename_expression ren e) in
	 { ini with desc = desc } in
       let i_list = List.map index i_list in
       let init_list = List.map init init_list in
       let b_eq_list = rename_block ren b_eq_list in
       EQforall { body with for_index = i_list; for_init = init_list;
			    for_body = b_eq_list }
    | EQblock _ | EQautomaton _ | EQpresent _ 
    | EQemit _ | EQder _ | EQnext _ -> assert false in
  { eq with eq_desc = desc }

and rename_equation_list ren eq_list = List.map (rename_equation ren) eq_list

and rename_block ren ({ b_body = eq_list } as b) =
  let eq_list = rename_equation_list ren eq_list in
  { b with b_body = eq_list }

and apply x ren =
  try Env.find x ren with | Not_found -> x
					   
(* The main functions *)
let local ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, { env = env; ren = ren } = equation_list eq_list in
  let eq_list = rename_equation_list ren eq_list in
  { l with l_eq = eq_list; l_env = Env.append env l_env }

let expression ({ e_desc = desc } as e) =
  let desc =
    match desc with
    | Elet(l, e) -> Elet(local l, e)
    | _ -> desc in
  { e with e_desc = desc }

let implementation impl =
  match impl.desc with
  | Econstdecl(n, is_static, e) ->
     { impl with desc = Econstdecl(n, is_static, expression e) }
  | Efundecl(n, ({ f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = expression e }) }
  | _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list
