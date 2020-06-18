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

(* compute write variables for every equation and block. Variables which *)
(* are written only once and stay local to the block where they appear   *)
(* get kind [Sval]. Otherwise, they get kind Svar or Smem *)

open Ident
open Zelus
open Deftypes

(* merge of two sets of defined names. If a name appears in one branch only *)
(* it must be a shared variable *)
let merge ({ dv = dv1 } as def1, s1) ({ dv = dv2 } as def2, s2) =
  Total.union def1 def2, S.union dv1 (S.union dv2 (S.union s1 s2))

(* union of two sets of defined names. If a name appears twice, it must *)
(* be a shared variable *)
let union ({ dv = dv1 } as def1, s1) ({ dv = dv2 } as def2, s2) =
  Total.union def1 def2,
  S.union (S.inter dv1 dv2) (S.union s1 s2)
  
(* given [b_env], returns the set of defined names and a *)
(* new env., equal to [b_env] but where the kind of variables not in the *)
(* set of shared variables [shared_set] is turned to [Sval] *)
let filter_env shared_set b_env =
  let filter n ({ t_sort = sort } as entry) (bounded, env) =
    let entry =
      match sort with
	| (Svar { v_combine = None; v_default = None }
	  | Smem { m_kind = None; m_init = Noinit; m_previous = false;
		   m_combine = None })
	    when not (S.mem n shared_set) -> { entry with t_sort = Sval }
	| _ -> entry in
    S.add n bounded, Env.add n entry env in
  Env.fold filter b_env (S.empty, Env.empty)
  			
let rec equation ({ eq_desc = desc } as eq) =
  let eq, defnames, shared_set = match desc with
    | EQeq(pat, e) ->
       { eq with eq_desc = EQeq(pat, expression e) },
       { Deftypes.empty with dv = Vars.fv_pat S.empty S.empty pat }, S.empty
    | EQpluseq(n, e) ->
       { eq with eq_desc = EQpluseq(n, expression e) },
       { Deftypes.empty with dv = S.singleton n }, S.empty
    | EQder(n, e, None, []) ->
       { eq with eq_desc = EQder(n, expression e, None, []) },
       { Deftypes.empty with der = S.singleton n }, S.empty
    | EQinit(n, e) ->
       { eq with eq_desc = EQinit(n, expression e) },
       { Deftypes.empty with di = S.singleton n }, S.empty
    | EQmatch(total, e, m_h_list) ->
       let m_h_list, (defnames, shared_set) =
	 Misc.map_fold
	   (fun acc ({ m_body = b } as m_h) ->
	    let b, defnames, shared_set = block b in
	    { m_h with m_body = b }, merge (defnames, shared_set) acc)
	   (Deftypes.empty, S.empty) m_h_list in
       { eq with eq_desc = EQmatch(total, expression e, m_h_list) },
       defnames, shared_set
    | EQreset(eq_list, e) ->
       let eq_list, (defnames, shared_set) =
	 equation_list (Deftypes.empty, S.empty) eq_list in
       let defnames, shared_set =
	 merge (defnames, shared_set) (Deftypes.empty, S.empty) in
       { eq with eq_desc = EQreset(eq_list, expression e) },
       defnames, shared_set
    | EQand(and_eq_list) ->
       let and_eq_list, (defnames, shared_set) =
	 equation_list (Deftypes.empty, S.empty) and_eq_list in
       { eq with eq_desc = EQand(and_eq_list) }, defnames, shared_set
    | EQbefore(before_eq_list) ->
       let before_eq_list, (defnames, shared_set) =
	 equation_list (Deftypes.empty, S.empty) before_eq_list in
       { eq with eq_desc = EQbefore(before_eq_list) }, defnames, shared_set
    | EQblock(b) ->
       let b, defnames, shared_set = block b in
       { eq with eq_desc = EQblock(b) }, defnames, shared_set
    | EQforall ({ for_index = i_list; for_init = init_list;
		  for_body = b_eq_list } as body) ->
       (* compute the association table [xi_out_x] from the *)
       (* list of [xi out x] pairs *)
       let index xi_out_x ({ desc = desc } as ind) =
	 match desc with
	 | Einput(i, e) ->
	    { ind with desc = Einput(i, expression e) }, xi_out_x 
	 | Eindex(i, e1, e2) ->
	    { ind with desc = Eindex(i, expression e1, expression e2) },
	    xi_out_x
	 | Eoutput(xi, x) ->
	    ind, Env.add xi x xi_out_x in
       (* computes the set of initialized names [i_set] *)
       let init acc ({ desc = desc } as ini) =
	 match desc with
	 | Einit_last(i, e) ->
	    { ini with desc = Einit_last(i, expression e) }, S.add i acc in
       let i_list, xi_out_x = Misc.map_fold index Env.empty i_list in
       let init_list, i_set = Misc.map_fold init S.empty init_list in
       let b_eq_list, { dv = dv; di = di; der = der; nv = nv; mv = mv },
           shared_set = block b_eq_list in
       (* if [xi in defnames_in_body] and [xi out x] then [x in defnames] *)
       (* if [xi in shared_set] and [xi out x] or [x in shared_set] *)
       let x_of_xi xi =
           try Env.find xi xi_out_x  with Not_found -> xi in
       let defnames =
	 { dv = S.map x_of_xi dv; di = S.map x_of_xi di;
	   der = S.map x_of_xi der; nv = S.map x_of_xi nv;
           mv = S.map x_of_xi mv } in
       let shared_set = S.map x_of_xi shared_set in
       (* all variables defined in the body of the loop are shared *)
       let defnames, shared_set =
	 merge (defnames, shared_set) (Deftypes.empty, S.empty) in
       { eq with eq_desc =
		   EQforall { body with for_index = i_list; for_init = init_list;
					for_body = b_eq_list } },
       defnames, shared_set
    | EQpresent _ | EQautomaton _ | EQder _
    | EQnext _ | EQemit _ -> assert false in
  (* set the names defined in the equation *)
  { eq with eq_write = defnames }, defnames, shared_set

and equation_list acc eq_list = 
  Misc.map_fold
    (fun acc eq -> let eq, defnames, shared_set = equation eq in
		   eq, union (defnames, shared_set) acc) acc eq_list       

and block ({ b_env = b_env; b_locals = l_list; b_body = eq_list } as b) =
  let l_list = List.map local l_list in
  let eq_list, ({ dv = dv; der = der; di = di; nv = nv; mv = mv }, shared_set) =
    equation_list (Deftypes.empty, S.empty) eq_list in
  let bounded, b_env = filter_env shared_set b_env in
  let dv = S.diff dv bounded in
  let di = S.diff di bounded in
  let der = S.diff der bounded in
  let nv = S.diff nv bounded in
  let mv = S.diff mv bounded in
  let shared_set = S.diff shared_set bounded in
  let local_defnames = { dv = dv; der = der; di = di; nv = nv; mv = mv } in
  { b with b_write = local_defnames; b_locals = l_list;
	   b_env = b_env; b_body = eq_list },
  local_defnames, shared_set
	      
  
and local ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, (_, shared_set) =
    equation_list (Deftypes.empty, S.empty) eq_list in
  let _, l_env = filter_env shared_set l_env in
  { l with l_eq = eq_list; l_env = l_env }

and expression ({ e_desc = desc } as e) =
  let desc =
    match desc with
    | Elocal _ | Eglobal _ 
    | Econst _ | Econstr0 _ | Elast _ -> desc
    | Eop(op, e_list) ->
       Eop(op, List.map expression e_list)
    | Eapp(app, op, e_list) ->
       Eapp(app, op, List.map expression e_list)
    | Etuple(e_list) -> Etuple(List.map expression e_list)
    | Econstr1(c, e_list) -> Econstr1(c, List.map expression e_list)
    | Erecord_access(e_record, ln) -> Erecord_access(expression e_record, ln)
    | Erecord(l_e_list) ->
       Erecord(List.map (fun (l, e) -> (l, expression e)) l_e_list)
    | Erecord_with(e_record, l_e_list) ->
       Erecord_with(expression e_record,
		    List.map (fun (l, e) -> (l, expression e)) l_e_list)
    | Etypeconstraint(e, ty) -> Etypeconstraint(expression e, ty)
    | Elet(l, e) -> Elet(local l, expression e)
    | Eblock(b, e) -> let b, _, _ = block b in Eblock(b, expression e)
    | Eseq(e1, e2) -> Eseq(expression e1, expression e2)
    | Eperiod { p_phase = p1; p_period = p2 } ->
       Eperiod
	 { p_phase = Misc.optional_map expression p1; p_period = expression p2 }
    | Epresent _ | Ematch _ -> assert false in
  { e with e_desc = desc }

let implementation impl =
  match impl.desc with
  | Econstdecl(n, is_static, e) ->
     { impl with desc = Econstdecl(n, is_static, expression e) }
  | Efundecl(n, ({ f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = expression e }) }
  | _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list
