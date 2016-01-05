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
(* causality check *)

(* C | H |-c e: ct [e] has causality [ct] with the invariant that *)
(* [forall ci in ct. ci < c]] *)
(* [C] is a constraint and [H] is an environment *)

(* The relation c1 < c2 means that c1 must be computed before c2 *)
(* The causality analysis is able to express that a block executes atomically, *)
(* that is, it is considered as iff all output instantaneously depend on *)
(* all input *)
(* For the moment, all control structure follow this "atomic" constraint. This *)
(* may evolve if code-generation is changed. *)
(* Extra rules are: *)
(* 1. for a sequence of declarations, the sequential order is preserved. *)
(*    [let x1 = e1 in let x2 = e2 in do x = e] *)
(*    - x1: t1, x2: t2, x: t with t1 < t2 < t *)
(* 2. for a control-structure, [if x then do x1 = e1 and x2 = e2 done *)
(*                              else do x1 = e'1 and x2 = e'2 done *)
(*    - x: t[a] *)
(*    - [x1: t1[b]; x2: t2[b] ] < [x1: t1'[b]; x2: t2'[b]] with a < b *)
 (* 3. The same rule applies for all control-structures (present/automata) *)

open Misc
open Ident
open Global
open Zelus
open Location
open Deftypes
open Defcaus
open Pcaus
open Causal
open Causal.Cenv

let print x = Misc.internal_error "unbound" Printer.name x

(* Main error message *)
      
(* dependence cycle and the current typing environment *)
exception Error of location * centry Env.t * Causal.error

let error loc env kind = raise (Error(loc, env, kind))

let message loc env kind =
  begin
    match kind with
    | ClashLast(x) ->
       Format.eprintf
	 "@[%aCausality error: last %s is read in a continuous context \n\
          while %s is not a continuous state variable nor piecewise constant.@.@]"
         output_location loc (Ident.source x) (Ident.source x)
    | ClashTypes(left_tc, right_tc, cycle) ->
       let cset = Cenv.vars env in
       let cycle = Causal.shrink cset cycle in
       Format.eprintf "@[%aCausality error: this expression \
                       may instantaneously depend on itself.@.\
                       Here is an example of a cycle:@.@[%a@]@.@]"
                      output_location loc
                      Pcaus.cycle cycle;
       if !Misc.verbose
       then Format.eprintf "@[This expression has causality type@ @[%a@]@ \
                            whereas it should be less than@ @[%a@]@.\
                            The current typing environment is:@.@[%a@]@]"
			   Cenv.ptype left_tc
			   Cenv.ptype right_tc
			   Cenv.penv env
  end;
  raise Misc.Error

(** Typing a pattern. It returns an environment *)
let rec pattern ({ p_desc = desc; p_loc = loc } as p) tc =
  try
    let env = match desc with
      | Ewildpat | Econstpat _ | Econstr0pat _ -> Env.empty
      | Evarpat(x) ->
         Env.singleton x (Causal.annotate (Cname x) tc)
      | Etuplepat(pat_list) ->
         let tc_list = Causal.filter_product (List.length pat_list) tc in
         List.fold_left2
	   (fun acc pat tc -> Env.append (pattern pat tc) acc)
	   Env.empty pat_list tc_list
      | Erecordpat(l) ->
         let c = Causal.new_var () in
         Causal.synchronise c tc;
         List.fold_left
	   (fun acc (_, p) -> Env.append (pattern p (Causal.atom c)) acc)
	   Env.empty l
      | Etypeconstraintpat(p, _) -> pattern p tc
      | Eorpat(p, _) -> pattern p tc
      | Ealiaspat(p, x) ->
         let tc = Causal.annotate (Cname x) tc in
	 Env.add x tc (pattern p tc) in
    (* annotate the pattern with causality information *)
    p.p_caus <- S.elements (Causal.vars S.empty tc);
    env
  with
  | Causal.Error err -> error loc Env.empty err

(** Build an environment from a typing environment. *)
let build_env expected_k l_env =
   let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } acc =
     let cur_tc = Causal.annotate (Cname n) (Causal.skeleton ty) in
     let last_tc = Causal.annotate (Clast n) (Causal.skeleton ty) in
     Env.add n { last = false; cur_tc = cur_tc; last_tc = last_tc } acc in
   Env.fold entry l_env Env.empty

(** Causality analysis of a match handler.*)
let match_handlers body expected_k before_c env m_h_list =
  let handler { m_pat = p; m_body = b } =
    let c_e = Causal.new_var () in
    let m_env = pattern p (skeleton_on_c c_e p.p_typ) in
    let m_env = Cenv.make expected_k m_env in
    let env = Env.append m_env env in
    body expected_k before_c env b in
  List.map handler m_h_list

(** Causality analysis of a present handler *)
let present_handlers scondpat body expected_k before_c env p_h_list h_opt =
  let handler { p_cond = scpat; p_body = b } =
    let c, new_env = scondpat expected_k before_c env scpat in
    let env = Env.append new_env env in
    body (Types.lift_to_discrete expected_k) before_c env b in
  let tc_list = List.map handler p_h_list in
  match h_opt with
  | None -> tc_list | Some(h) -> (body expected_k before_c env h) :: tc_list

(* [last x] is valid if [ltc < tc] *)
let type_of_last loc expected_k ({ last_tc = ltc } as centry) =
  match expected_k with
  | Tcont -> centry.last <- true; ltc | _ -> ltc
					      
(** causality of an expression. [C | H |-before_c e: ct] *)
let rec exp expected_k before_c env
	    ({ e_desc = desc; e_typ = ty; e_loc = loc } as e) =
  try
    let tc = match desc with
      | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> Causal.skeleton ty
      | Elocal(x) ->
         begin try
             let { cur_tc = tc } = Env.find x env in tc
           with | Not_found -> print x
         end
      | Elast(x) ->
         let centry = try Env.find x env with | Not_found -> print x in
	 type_of_last loc expected_k centry
      | Etuple(e_list) ->
         product (List.map (exp expected_k before_c env) e_list)
      | Eapp(op, e_list) ->
         apply expected_k before_c env op ty e_list
      | Erecord_access(e_record, _) ->
         let c = Causal.new_var () in
         exp_before_on_c expected_k before_c env e_record c;
         Causal.skeleton_on_c c ty
      | Erecord(l) ->
         let c = Causal.new_var () in
         List.iter
	   (fun (_, e) -> exp_before_on_c expected_k before_c env e c) l;
         Causal.skeleton_on_c c ty
      | Etypeconstraint(e, _) -> exp expected_k before_c env e
      | Elet(l, e_let) ->
         let new_env = local expected_k before_c env l in
         let tc = exp expected_k before_c (Env.append new_env env) e_let in
         tc
      | Eseq(e1, e2) ->
         let c = Causal.new_var () in
         exp_before_on_c expected_k before_c env e1 c;
         exp_before_on_c expected_k before_c env e2 c;
         Causal.skeleton_on_c c e2.e_typ
      | Epresent(h_e_list, e_opt) ->
         present_handler_exp_list expected_k before_c env h_e_list e_opt
      | Ematch(_, e, h_e_list) ->
         let c_e = Causal.new_var () in
         exp_before_on_c expected_k before_c env e c_e;
         let tc = match_handler_exp_list expected_k before_c env h_e_list in
	 Causal.supc c_e tc in
    (* check that [forall ci in ct. ci < before_c] *)
    let cset = Causal.vars S.empty tc in
    S.iter (fun ci -> Causal.ctype_before_ctype ci before_c) cset;
    (* annotate [e] with causality variables *)
    e.e_caus <- S.elements cset;
    tc
  with
  | Causal.Error err -> error loc env err

(** Typing an application *)
and apply expected_k before_c env op ty e_list =
  let c = Causal.new_var () in
  match op, e_list with
  | Eunarypre, [e] ->
     exp_before_on_c expected_k before_c env e before_c;
     Causal.skeleton_on_c c ty
  | Efby, [e1;e2] ->
     exp_before_on_c expected_k before_c env e2 (Causal.new_var ());
     exp_before_on_c expected_k before_c env e1 c;
     Causal.skeleton_on_c c ty
  | Eminusgreater, [e1;e2] ->
     exp_before_on_c expected_k before_c env e1 c;
     exp_before_on_c expected_k before_c env e2 c;
     Causal.skeleton_on_c c ty
  | Eifthenelse, [e1; e2; e3] ->
     exp_before_on_c expected_k before_c env e1 c;
     exp_before_on_c expected_k before_c env e2 c;
     exp_before_on_c expected_k before_c env e3 c;
     Causal.skeleton_on_c c ty
  | Eup, [e] -> (* [up(e)] does not depend instantaneously of itself *)
     exp_before_on_c expected_k before_c env e before_c;
     Causal.skeleton_on_c c ty
  | (Einitial | Etest | Edisc), e_list ->
     List.iter
       (fun e ->
        exp_before_on_c expected_k before_c env e c) e_list;
     Causal.skeleton_on_c c ty
  | Eop(_, lname), e_list ->
     let { info = info } = Modules.find_value lname in
     let tc_arg_list, tc_res = Causal.instance info in
     List.iter2 (exp_before expected_k before_c env) e_list tc_arg_list;
     tc_res
  | Eevery(_, lname), e :: e_list ->
     let { info = info } = Modules.find_value lname in
     let tc_arg_list, tc_res = Causal.instance info in
     List.iter2 (exp_before expected_k before_c env) e_list tc_arg_list;
     exp_before_on_c expected_k before_c env e c;
     Causal.type_before_type (Causal.skeleton_on_c c ty) tc_res;
     tc_res
  | _ -> assert false

and exp_before_on_c expected_k before_c env e expected_c =
  try
    let actual_tc = exp expected_k before_c env e in
    let expected_tc = Causal.skeleton_on_c expected_c e.e_typ in
    Causal.type_before_type actual_tc expected_tc;
    (* annotate [e] with causality variables *)
    e.e_caus <- [expected_c]
  with
  | Causal.Error err -> error e.e_loc env err

and exp_before expected_k before_c env e expected_tc =
  try
    let actual_tc = exp expected_k before_c env e in
    Causal.type_before_type actual_tc expected_tc;
    (* annotate [e] with causality variables *)
    e.e_caus <- S.elements (Causal.vars S.empty expected_tc)
  with
  | Causal.Error err -> error e.e_loc env err

(** Checking equations *)
and equation_list expected_k before_c env eq_list =
  List.fold_left
    (fun acc eq ->
     Cenv.sup acc (equation expected_k before_c env eq)) Env.empty eq_list

and equation expected_k before_c env
    { eq_desc = desc; eq_write = defnames; eq_loc = loc } =
  match desc with
    | EQeq(p, e) ->
        let tc_e = exp expected_k before_c env e in
        Cenv.make expected_k (pattern p tc_e)
    | EQpluseq(n, e) ->
        let tc_e = Causal.annotate (Cname n) (exp expected_k before_c env e) in
	Cenv.make expected_k (Env.singleton n tc_e)
    | EQder(n, e, e0_opt, h_e_list) ->
        (* no causality constraint for [e] *)
        ignore (exp expected_k before_c env e);
        (* type the initialization and handler *)
        let tc_opt =
          match h_e_list with
          | [] -> None
          | _ ->
	     Some(present_handler_exp_list expected_k before_c env h_e_list None) in
	let ltc_opt =
          Misc.optional_map
	    (exp (Types.lift_to_discrete expected_k) before_c env) e0_opt in
	(* no environment is produced when only the derivative is defined *)
	let env =
	  match tc_opt, ltc_opt with
	  | None, None -> Env.empty
	  | Some(tc), None ->
	     Env.singleton n { last = true; cur_tc = tc; last_tc = fresh tc }
	  | None, Some(ltc) ->
	     Env.singleton n { last = true; cur_tc = fresh ltc; last_tc = ltc }
	  | Some(tc), Some(ltc) ->
	     Env.singleton n { last = true; cur_tc = tc; last_tc = ltc } in
	env
    | EQinit(n, e0) ->
       let ltc = Causal.annotate (Clast n) (exp expected_k before_c env e0) in
       let tc = Causal.annotate (Cname n) (fresh ltc) in
       Env.singleton n { last = true; cur_tc = tc; last_tc = ltc }
    | EQnext(n, e, e0_opt) ->
        ignore (exp expected_k before_c env e);
        let tc = Causal.skeleton_on_c (Causal.new_var ()) e.e_typ in
        let tc = Causal.annotate (Cname n) tc in
	begin match e0_opt with
              | None -> () | Some(e0) -> exp_before expected_k before_c env e0 tc
        end;
        Env.singleton n { last = true; cur_tc = tc; last_tc = fresh tc }
    | EQautomaton(is_weak, s_h_list, se_opt) ->
        (* Typing a state expression *)
        let state env { desc = desc } =
          let c = Causal.new_var () in
          Causal.ctype_before_ctype c before_c;
	  match desc with
            | Estate0 _ -> ()
            | Estate1(_, e_list) ->
               List.iter
		 (fun e -> exp_before_on_c expected_k before_c env e c)
		 e_list in
        (* Typing of handlers *)
        (* scheduling is done this way: *)
        (* - Automata with strong preemption: *)
        (*   1. compute unless conditions; *)
        (*   2. execute the corresponding handler. *)
        (* - Automata with weak preemption: *)
        (*   1. compute the body; 2. compute the next active state. *)
        let handler expected_k env { s_body = b; s_trans = trans; s_env = s_env } =
          (* typing an escape. *)
          let escape env { e_cond = sc; e_block = b_opt; e_next_state = ns } =
            let c_e, new_env = scondpat expected_k before_c env sc in
            let env = Env.append new_env env in
            let env, shared_env =
              match b_opt with
              | None -> env, Env.empty
              | Some(b) ->
                 block_eq_list
		   (Types.lift_to_discrete expected_k) before_c env b in
            state env ns;
            Cenv.supc c_e shared_env in
          let s_env = build_env expected_k s_env in
          let env = Env.append s_env env in
          if is_weak then
            let env, shared_env = block_eq_list expected_k before_c env b in
            let trans_env =
              Cenv.suplist (List.map (escape env) trans) in
            Env.append shared_env trans_env
          else
            let trans_env =
              Cenv.suplist (List.map (escape env) trans) in
            let _, shared_env = block_eq_list expected_k before_c env b in
            Env.append shared_env trans_env in
        (* a shared variable [x] defined in [s_h_list] can potentially *)
        (* be accessed with [last x] *)
        let env = Cenv.last defnames env in
        let new_env =
          Cenv.suplist (List.map (handler expected_k env) s_h_list) in
        ignore (Misc.optional_map (state env) se_opt);
        new_env
    | EQmatch(_, e, m_h_list) ->
       let c_e = Causal.new_var () in
       exp_before_on_c expected_k before_c env e c_e;
       (* a shared variable [x] defined in [m_h_list] can potentially *)
       (* be accessed with [last x] *)
       let env = Cenv.last defnames env in
       let env = match_handler_block_eq_list expected_k before_c env m_h_list in
       Cenv.supc c_e env
    | EQpresent(p_h_list, b_opt) ->
       (* a shared variable [x] defined in [p_h_list] can potentially *)
       (* be accessed with [last x] *)
       let env = Cenv.last defnames env in
       present_handler_block_eq_list expected_k before_c env p_h_list b_opt
    | EQreset(eq_list, e) ->
       let c_e = Causal.new_var () in
       exp_before_on_c expected_k before_c env e c_e;
       let env = equation_list expected_k before_c env eq_list in
       Cenv.supc c_e env
    | EQemit(n, e_opt) ->
       let c_e = Causal.new_var () in
       Misc.optional_unit
	 (fun _ e -> exp_before_on_c expected_k before_c env e c_e) () e_opt;
       let tc = Causal.annotate (Cname n) (atom c_e) in
       Cenv.make expected_k (Env.singleton n tc)
    | EQblock(b_eq_list) ->
       let _, shared_env = block_eq_list expected_k before_c env b_eq_list in
       shared_env

(* Typing a present handler for expressions *)
(* The handler list is not be empty *)
and present_handler_exp_list expected_k before_c env p_h_list e_opt =
  let before_local_c = Causal.new_var () in
  Causal.ctype_before_ctype before_local_c before_c;
  let tc_list = present_handlers scondpat exp expected_k before_local_c env p_h_list e_opt in
  Causal.supc before_local_c (Causal.sup_list tc_list)

(* Typing a present handler for blocks *)
and present_handler_block_eq_list expected_k before_c env p_h_list p_h_opt =
  let before_local_c = Causal.new_var () in
  Causal.ctype_before_ctype before_local_c before_c;
  let block_eq_list expected_k before_c env b_eq_list =
    let _, shared_env = block_eq_list expected_k before_c env b_eq_list in
    shared_env in
  let env_list =
    present_handlers
      scondpat block_eq_list expected_k before_local_c env p_h_list p_h_opt in
  Cenv.supc before_local_c (Cenv.suplist env_list)

(* Typing a match handler for expressions *)
(* The handler list is not empty *)
and match_handler_exp_list expected_k before_c env m_h_list =
  let tc_list = match_handlers exp expected_k before_c env m_h_list in
  Causal.sup_list tc_list

(* Typing a match handler for blocks. *)
and match_handler_block_eq_list expected_k before_c env m_h_list =
  let block_eq_list expected_k before_c env b_eq_list =
    let _, shared_env = block_eq_list expected_k before_c env b_eq_list in
    shared_env in
  let new_env_list = match_handlers block_eq_list expected_k before_c env m_h_list in
  Cenv.suplist new_env_list

(* Typing a block with a set of equations in its body. Returns *)
(* the pair [env, shared_env] *)
(* [env] is the environment of variable defined globally plus local variables *)
(* [shared_env] is the variables between the [do ... done] *)
(* [expected_k] is the expected kind for the body. *)
and block_eq_list expected_k before_c env
    { b_locals = l_list; b_body = eq_list;
      b_env = b_env; b_loc = loc; b_write = defnames } =
  (* the block is executed atomically *)
  (* local equations are executed sequentially before the body *)
  let before_local_c = Causal.new_var () in
  let before_block_c = Causal.new_var () in
  Causal.ctype_before_ctype before_local_c before_block_c;
  Causal.ctype_before_ctype before_block_c before_c;
  (* typing local definitions *)
  let local before_c local_env l =
    let before_local_c = Causal.new_var () in
    Causal.ctype_before_ctype before_local_c before_c;
    let new_env = local expected_k before_local_c local_env l in
    let new_env = Cenv.supc before_local_c new_env in
    Env.append new_env local_env in
  let env = Cenv.last defnames env in
  let env = List.fold_left (local before_local_c) env l_list in
  (* Build the typing environment for names introduced by a *)
  (* [local x1,..., xn in ...] *)
  let b_env = build_env expected_k b_env in
  let env = Env.append b_env env in
  try
    let shared_env = equation_list expected_k before_block_c env eq_list in
    let shared_env = Cenv.supc before_local_c shared_env in
    (* detect causality cycles inside the block *)
    let shared_env = Cenv.before shared_env env in
    env, Cenv.supc before_block_c shared_env
  with Causal.Error err -> error loc env err

(* Typing a local declaration. Returns the environment of local variables *)
and local expected_k before_c env { l_eq = eq_list; l_env = l_env; l_loc = loc } =
  (* First extend the typing environment *)
  let l_env = build_env expected_k l_env in
  let env = Env.append l_env env in
  (* Then type the body *)
  try
    let new_env = equation_list expected_k before_c env eq_list in
    let new_env = Cenv.before new_env l_env in
    new_env
  with Causal.Error err -> error loc env err

(* Typing  a signal pattern. *)
and scondpat expected_k before_c env sc =
  let rec scondpat c { desc = desc; loc = loc } =
    match desc with
    | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
        Cenv.sup (scondpat c sc1) (scondpat c sc2)
    | Econdon(sc1, e) ->
       exp_before_on_c expected_k before_c env e c;
       scondpat c sc1
    | Econdexp(e) ->
       exp_before_on_c expected_k before_c env e c; Env.empty
    | Econdpat(e, p) ->
       exp_before_on_c expected_k before_c env e c;
       let ty = Causal.skeleton_on_c c p.p_typ in
       Cenv.make expected_k (pattern p ty) in
  let c = Causal.new_var () in
  c, scondpat c sc

let implementation ff { desc = desc } =
  try
    match desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(_, e) ->
       Misc.push_binding_level ();
       ignore (exp Deftypes.Tany (Causal.new_var ()) Env.empty e);
       Misc.pop_binding_level ()
    | Efundecl (f, { f_kind = k; f_atomic = atomic; f_args = pat_list;
                     f_body = e; f_env = h0 }) ->
       Misc.push_binding_level ();
       let expected_k = Interface.kindtype k in
       let tc_arg_list, tc_res =
         (* for an atomic node, all outputs depend on all inputs *)
         if atomic then
           (* first type the body *)
	   let c_in = Causal.new_var () in
	   let c_res = Causal.new_var () in
	   Causal.ctype_before_ctype c_in c_res;
	   List.map (fun p -> Causal.skeleton_on_c c_in p.p_typ) pat_list,
           Causal.skeleton_on_c c_res e.e_typ
         else
           List.map (fun p -> Causal.skeleton p.p_typ) pat_list,
           Causal.skeleton e.e_typ in
       let before_c = Causal.new_var () in
       let env =
         List.fold_left2
	   (fun acc p ty -> Env.append (Cenv.make expected_k (pattern p ty)) acc)
           Env.empty pat_list tc_arg_list in
       exp_before expected_k before_c env e tc_res;
       Misc.pop_binding_level ();
       let tcs = generalise tc_arg_list tc_res in
       (* then add the current entries in the global environment *)
       Global.set_causality (Modules.find_value (Lident.Name(f))) tcs;
       (* output the signature *)
       if !Misc.print_causality then Pcaus.declaration ff f tcs
  with
  | Error(loc, env, err) -> message loc env err

let implementation_list ff impl_list = List.iter (implementation ff) impl_list
