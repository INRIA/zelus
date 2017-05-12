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
(* causality check *)

(* C | H |- e: ct *)
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
       (* keep only names in cycle that either appear in the *)
       (* typing environment or one of the two types *)
       let cset = Cenv.mark true S.empty env in
       let cset = Causal.mark true (Causal.mark true cset left_tc) right_tc in
       let cycle = Causal.shrink_cycle cset cycle in
       Format.eprintf "@[%aCausality error: This expression \
                            has causality type@ @[%a@]@ \
                            whereas it should be less than@ @[%a@]@.\
                            Here is an example of a cycle:@.@[%a@]@.\
                            The current typing environment is:@.@[%a@]@]"
			   output_location loc
                           Pcaus.ptype left_tc
			   Pcaus.ptype right_tc
			   Pcaus.cycle cycle
                           (Cenv.penv cset) env
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

(** Build an environment with all entries synchronised on [c] *)
let build_env_on_c expected_k c l_env =
   let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } acc =
     let cur_tc = Causal.annotate (Cname n) (Causal.skeleton_on_c c ty) in
     let last_tc = Causal.annotate (Clast n) (Causal.skeleton_on_c c ty) in
     Env.add n { last = false; cur_tc = cur_tc; last_tc = last_tc } acc in
   Env.fold entry l_env Env.empty

(** Causality analysis of a match handler.*)
let match_handlers body expected_k env m_h_list =
  let handler { m_pat = p; m_body = b } =
    let c_e = Causal.new_var () in
    let m_env = pattern p (skeleton_on_c c_e p.p_typ) in
    let m_env = Cenv.make expected_k m_env in
    let env = Env.append m_env env in
    body expected_k env b in
  List.map handler m_h_list

(** Causality analysis of a present handler *)
let present_handlers scondpat body expected_k env p_h_list h_opt =
  let handler { p_cond = scpat; p_body = b } =
    let c, new_env = scondpat expected_k env scpat in
    let env = Env.append new_env env in
    body (Types.lift_to_discrete expected_k) env b in
  let tc_list = List.map handler p_h_list in
  match h_opt with
  | None -> tc_list | Some(h) -> (body expected_k env h) :: tc_list

(* [last x] is valid if [ltc < tc] *)
let type_of_last loc expected_k ({ last_tc = ltc } as centry) =
  match expected_k with
  | Tcont -> centry.last <- true; ltc | _ -> ltc
					      
(** causality of an expression. [C | H |-k e: ct] *)
let rec exp expected_k env
	    ({ e_desc = desc; e_typ = ty; e_loc = loc } as e) =
  try
    let tc = match desc with
      | Econst _ | Econstr0 _ | Eperiod _ -> Causal.skeleton ty
      | Eglobal { lname = lname } ->
	 let { info = info } = Modules.find_value lname in
	 Causal.instance info ty
      | Elocal(x) ->
         begin try
             let { cur_tc = tc } = Env.find x env in tc
           with | Not_found -> print x
         end
      | Elast(x) ->
         let centry = try Env.find x env with | Not_found -> print x in
	 type_of_last loc expected_k centry
      | Etuple(e_list) ->
         product (List.map (exp expected_k env) e_list)
      | Eop(op, e_list) ->
	 operator expected_k env op ty e_list
      | Eapp(_, e, e_list) ->
	 app expected_k env (exp expected_k env e) e_list
      | Erecord_access(e_record, _) ->
         let c = Causal.new_var () in
         exp_before_on_c expected_k env e_record c;
         Causal.skeleton_on_c c ty
      | Erecord(l) ->
         let c = Causal.new_var () in
         List.iter
	   (fun (_, e) -> exp_before_on_c expected_k env e c) l;
         Causal.skeleton_on_c c ty
      | Etypeconstraint(e, _) -> exp expected_k env e
      | Elet(l, e_let) ->
         let new_env = local expected_k env l in
         let tc = exp expected_k new_env e_let in
         tc
      | Eblock(b, e_block) ->
         let _, new_env = block_eq_list expected_k env b in
         let tc = exp expected_k (Env.append new_env env) e_block in
         tc
      | Eseq(e1, e2) ->
         let c = Causal.new_var () in
         exp_before_on_c expected_k env e1 c;
         exp_before_on_c expected_k env e2 c;
         Causal.skeleton_on_c c e2.e_typ
      | Epresent(h_e_list, e_opt) ->
         present_handler_exp_list expected_k env h_e_list e_opt
      | Ematch(_, e, h_e_list) ->
         let c_e = Causal.new_var () in
         exp_before_on_c expected_k env e c_e;
         let tc = match_handler_exp_list expected_k env h_e_list in
	 Causal.supc c_e tc in
    (* check that [forall ci in ct. ci < before_c] *)
    let cset = Causal.vars S.empty tc in
    (* annotate [e] with causality variables *)
    e.e_caus <- S.elements cset;
    tc
  with
  | Causal.Error err -> error loc env err

(** Typing an application *)
and app expected_k env tc_fct arg_list =
  (* typing the list of arguments *)
  let rec args tc_fct = function
    | [] -> tc_fct
    | arg :: arg_list ->
       let tc1, tc2 = Causal.filter_arrow tc_fct in
       exp_before expected_k env arg tc1;
       args tc2 arg_list in
  args tc_fct arg_list
       
(** Typing an operator *)
and operator expected_k env op ty e_list =
  let c = Causal.new_var () in
  match op, e_list with
  | Eunarypre, [e] ->
     exp_before_on_c expected_k env e (Causal.new_var ());
     Causal.skeleton_on_c c ty
  | Efby, [e1;e2] ->
     exp_before_on_c expected_k env e2 (Causal.new_var ());
     exp_before_on_c expected_k env e1 c;
     Causal.skeleton_on_c c ty
  | Eminusgreater, [e1;e2] ->
     exp_before_on_c expected_k env e1 c;
     exp_before_on_c expected_k env e2 c;
     Causal.skeleton_on_c c ty
  | Eifthenelse, [e1; e2; e3] ->
     exp_before_on_c expected_k env e1 c;
     exp_before_on_c expected_k env e2 c;
     exp_before_on_c expected_k env e3 c;
     Causal.skeleton_on_c c ty
  | Eup, [e] ->
     (* [up(e)] does not depend instantaneously of itself *)
     exp_before_on_c expected_k env e (Causal.new_var ());
     Causal.skeleton_on_c c ty
  | Einitial, [] ->
     Causal.skeleton_on_c c ty 
  | (Etest | Edisc | Ehorizon), [e] ->
     exp_before_on_c expected_k env e c;
     Causal.skeleton_on_c c ty
  | Eaccess, [e1; e2] ->
     exp_before_on_c expected_k env e1 c;
     exp_before_on_c expected_k env e2 c;
     Causal.skeleton_on_c c ty
  | Eupdate, [e1; i; e2] ->
     exp_before_on_c expected_k env e1 c;
     exp_before_on_c expected_k env i c;
     exp_before_on_c expected_k env e1 c;
     Causal.skeleton_on_c c ty
  | _ -> assert false
     
		    
and exp_before_on_c expected_k env e expected_c =
  try
    let actual_tc = exp expected_k env e in
    let expected_tc = Causal.skeleton_on_c expected_c e.e_typ in
    Causal.type_before_type actual_tc expected_tc;
    (* annotate [e] with causality variables *)
    e.e_caus <- [expected_c]
  with
  | Causal.Error err -> error e.e_loc env err

and exp_before expected_k env e expected_tc =
  try
    let actual_tc = exp expected_k env e in
    Causal.type_before_type actual_tc expected_tc;
    (* annotate [e] with causality variables *)
    e.e_caus <- S.elements (Causal.vars S.empty expected_tc)
  with
  | Causal.Error err -> error e.e_loc env err

(** Checking equations *)
and equation_list expected_k env eq_list =
  List.fold_left
    (fun acc eq -> Cenv.sup acc (equation expected_k env eq)) Env.empty eq_list

(* Typing of an equation. [env |-expected_k e : env_e < before_c] *)
(* all computations must be performed before instant [before_c] *)
and equation expected_k env
    { eq_desc = desc; eq_write = defnames; eq_loc = loc } =
  match desc with
    | EQeq(p, e) ->
        let tc_e = exp expected_k env e in
        Cenv.make expected_k (pattern p tc_e)
    | EQpluseq(n, e) ->
        let tc_e = Causal.annotate (Cname n) (exp expected_k env e) in
	Cenv.make expected_k (Env.singleton n tc_e)
    | EQder(n, e, e0_opt, h_e_list) ->
        (* no causality constraint for [e] *)
        ignore (exp expected_k env e);
        (* type the handler *)
        let tc_opt =
          match h_e_list with
          | [] -> None
          | _ ->
	     Some(present_handler_exp_list expected_k env h_e_list None) in
	(* type the initialization *)
        let itc_opt =
          Misc.optional_map
	    (exp (Types.lift_to_discrete expected_k) env) e0_opt in
	(* no environment is produced when only the derivative is defined *)
	let env =
	  match tc_opt, itc_opt with
	  | None, None -> Env.empty
	  | Some(tc), None ->
	     Env.singleton n { last = true; cur_tc = tc; last_tc = fresh tc }
	  | None, Some(itc) ->
	     Env.singleton n { last = true; cur_tc = itc; last_tc = itc }
	  | Some(tc), Some(itc) ->
	     Env.singleton n { last = true; cur_tc = Causal.sup itc tc;
			       last_tc = itc } in
	env
    | EQinit(n, e0) ->
       let ltc = Causal.annotate (Clast n) (exp expected_k env e0) in
       let tc = Causal.annotate (Cname n) ltc in
       Env.singleton n { last = true; cur_tc = tc; last_tc = ltc }
    | EQnext(n, e, e0_opt) ->
        ignore (exp expected_k env e);
        let tc = Causal.skeleton_on_c (Causal.new_var ()) e.e_typ in
        let tc = Causal.annotate (Cname n) tc in
	begin match e0_opt with
              | None -> () | Some(e0) -> exp_before expected_k env e0 tc
        end;
        Env.singleton n { last = true; cur_tc = tc; last_tc = fresh tc }
    | EQautomaton(is_weak, s_h_list, se_opt) ->
        (* Typing a state expression *)
        let state env { desc = desc } =
          let c = Causal.new_var () in
          match desc with
            | Estate0 _ -> ()
            | Estate1(_, e_list) ->
               List.iter (fun e -> exp_before_on_c expected_k env e c) e_list in
        (* Typing of handlers *)
        (* scheduling is done this way: *)
        (* - Automata with strong preemption: *)
        (*   1. compute unless conditions; *)
        (*   2. execute the corresponding handler. *)
        (* - Automata with weak preemption: *)
        (*   1. compute the body; 2. compute the next active state. *)
        let handler expected_k env
		    { s_body = b; s_trans = trans; s_env = s_env } =
          (* typing an escape. *)
          let escape env { e_cond = sc; e_block = b_opt; e_next_state = ns } =
            let c_e, new_env = scondpat expected_k env sc in
            let env = Env.append new_env env in
            let env, shared_env =
              match b_opt with
              | None -> env, Env.empty
              | Some(b) ->
                 block_eq_list
		   (Types.lift_to_discrete expected_k) env b in
            state env ns;
            Cenv.supc c_e shared_env in
          let s_env = build_env expected_k s_env in
          let env = Env.append s_env env in
          if is_weak then
            let env, shared_env = block_eq_list expected_k env b in
            let trans_env =
              Cenv.suplist (List.map (escape env) trans) in
            Env.append shared_env trans_env
          else
            let trans_env =
              Cenv.suplist (List.map (escape env) trans) in
            let _, shared_env = block_eq_list expected_k env b in
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
       exp_before_on_c expected_k env e c_e;
       (* a shared variable [x] defined in [m_h_list] can potentially *)
       (* be accessed with [last x] *)
       let env = Cenv.last defnames env in
       let env = match_handler_block_eq_list expected_k env m_h_list in
       Cenv.supc c_e env
    | EQpresent(p_h_list, b_opt) ->
       (* a shared variable [x] defined in [p_h_list] can potentially *)
       (* be accessed with [last x] *)
       let env = Cenv.last defnames env in
       present_handler_block_eq_list expected_k env p_h_list b_opt
    | EQreset(eq_list, e) ->
       let c_e = Causal.new_var () in
       exp_before_on_c expected_k env e c_e;
       let env = equation_list expected_k env eq_list in
       Cenv.supc c_e env
    | EQand(and_eq_list) ->
       equation_list expected_k env and_eq_list 
    | EQbefore(before_eq_list) ->
       equation_list expected_k env before_eq_list 
    | EQemit(n, e_opt) ->
       let c_e = Causal.new_var () in
       Misc.optional_unit
	 (fun _ e -> exp_before_on_c expected_k env e c_e) () e_opt;
       let tc = Causal.annotate (Cname n) (atom c_e) in
       Cenv.make expected_k (Env.singleton n tc)
    | EQblock(b_eq_list) ->
       let _, shared_env = block_eq_list expected_k env b_eq_list in
       shared_env
    | EQforall { for_index = i_list; for_init = init_list; for_body = b_eq_list;
		 for_out_env = o_env } ->
       (* Build the typing environment for inputs/outputs *)
       (* and build an association table [oi out o] for all output pairs *)
       let index (io_env, oi2o) { desc = desc } =
	 match desc with
	 | Einput(x, e) ->
            let in_c = Causal.new_var () in
	    exp_before_on_c expected_k env e in_c;
	    let ty_arg, _ = Types.filter_vec e.e_typ in
	    let tc = Causal.skeleton_on_c in_c ty_arg in
	    Env.add x { last = false; cur_tc = tc; last_tc = fresh tc } io_env,
	    oi2o
	 | Eindex(x, e1, e2) ->
	    let in_c = Causal.new_var () in
	    exp_before_on_c expected_k env e1 in_c;
	    exp_before_on_c expected_k env e2 in_c;
            let tc = Causal.skeleton_on_c in_c e1.e_typ in
	    Env.add x { last = false; cur_tc = tc; last_tc = fresh tc } io_env,
	    oi2o
	 | Eoutput(oi, o) ->
	    let out_c = Causal.new_var () in
	    let { t_typ = ty } = Env.find oi o_env in
	    let tc = Causal.skeleton_on_c out_c ty in
	    Env.add oi { last = false; cur_tc = tc; last_tc = fresh tc } io_env,
	    Env.add oi o oi2o in

       (* replace an entry [oi, tc_i[out_c]] by [o, atom out_c] *)
       (* when [oi out o]. *)
       let out out_c oi2o shared_env =
         (* all the outputs should be computed before [out_c] *)
	 let out oi
		 ({ last = last; cur_tc = tc; last_tc = ltc } as entry) env =
	   try
             let o = Env.find oi oi2o in
             let cset = Causal.vars S.empty tc in
             S.iter (fun c -> ctype_before_ctype c out_c) cset;
             let tc = atom out_c in
             Env.add o { last = false; cur_tc = tc; last_tc = fresh tc } env
           with
             Not_found -> Env.add oi entry env in
         Env.fold out shared_env Env.empty in
       
       (* typing the initialization *)
       let init init_env { desc = desc } =
	 match desc with
	 | Einit_last(x, e) ->
	    let tc = exp expected_k env e in
	    Env.add x { last = true; cur_tc = fresh tc; last_tc = tc } init_env
	 | Einit_value(x, e, _) ->
	    let tc = exp expected_k env e in
	    Env.add x
                    { last = false; cur_tc = tc; last_tc = fresh tc } init_env in

       (* build the typing environment for read variables from the header *)
       let io_env, oi2o = List.fold_left index (Env.empty, Env.empty) i_list in

       (* build the typing environment for accummulation variables *)
       let init_env = List.fold_left init Env.empty init_list in

       (* build the typing environment *)
       let env = Env.append io_env env in
       let env = Env.append init_env env in
              
       (* type the body *)
       let _, shared_env = block_eq_list expected_k env b_eq_list in
       
       let shared_env =
	 try
	   Cenv.before shared_env (Env.append (Cenv.unlast init_env) env)
	 with Causal.Error err -> error loc env err in
       (* replace an entry [oi, ty_i[c]] by [o, atom(c)] when [oi out o] *)
       (* keep other entries. All outputs must be computed before [out_c] *)
       let out_c = Causal.new_var () in
       let shared_env = out out_c oi2o shared_env in
       shared_env

	 
(* Typing a present handler for expressions *)
(* The handler list is not be empty *)
and present_handler_exp_list expected_k env p_h_list e_opt =
  let tc_list =
    present_handlers scondpat exp expected_k env p_h_list e_opt in
  Causal.sup_list tc_list

(* Typing a present handler for blocks *)
and present_handler_block_eq_list expected_k env p_h_list p_h_opt =
  let block_eq_list expected_k env b_eq_list =
    let _, shared_env = block_eq_list expected_k env b_eq_list in
    shared_env in
  let env_list =
    present_handlers
      scondpat block_eq_list expected_k env p_h_list p_h_opt in
  Cenv.suplist env_list

(* Typing a match handler for expressions *)
(* The handler list is not empty *)
and match_handler_exp_list expected_k env m_h_list =
  let tc_list = match_handlers exp expected_k env m_h_list in
  Causal.sup_list tc_list

(* Typing a match handler for blocks. *)
and match_handler_block_eq_list expected_k env m_h_list =
  let block_eq_list expected_k env b_eq_list =
    let _, shared_env = block_eq_list expected_k env b_eq_list in
    shared_env in
  let new_env_list = match_handlers block_eq_list expected_k env m_h_list in
  Cenv.suplist new_env_list

(* Typing a block with a set of equations in its body. Returns *)
(* the pair [env, shared_env] *)
(* [env] is the environment of variable defined globally plus local variables *)
(* [shared_env] is the variables between the [do ... done] *)
(* [expected_k] is the expected kind for the body. *)
and block_eq_list expected_k env
    { b_locals = l_list; b_body = eq_list;
      b_env = b_env; b_loc = loc; b_write = defnames } =
  (* the block is executed atomically *)
  (* local equations are executed sequentially before the body *)
  (* typing local definitions *)
  let local local_env l =
    let new_env = local expected_k local_env l in
    let new_env = Cenv.suplist [new_env] in
    Env.append new_env local_env in
  let env = Cenv.last defnames env in
  let env = List.fold_left local env l_list in
  (* Build the typing environment for names introduced by a *)
  (* [local x1,..., xn in ...] *)
  let b_env = build_env expected_k b_env in
  let env = Env.append b_env env in
  try
    let shared_env = equation_list expected_k env eq_list in
    (* detect causality cycles inside the block *)
    let shared_env = Cenv.before shared_env env in
    env, Cenv.suplist [shared_env]
  with Causal.Error err -> error loc env err

(* Typing a local declaration. Returns the extended environment *)
and local expected_k env { l_eq = eq_list; l_env = l_env; l_loc = loc } =
  (* First extend the typing environment *)
  let l_env = build_env expected_k l_env in
  let env = Env.append l_env env in
  (* Then type the body *)
  try
    let new_env = equation_list expected_k env eq_list in
    let _ = Cenv.before new_env l_env in
    env
  with Causal.Error err -> error loc env err

(* Typing  a signal pattern. *)
and scondpat expected_k env sc =
  let rec scondpat expected_c { desc = desc; loc = loc } =
    match desc with
    | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
        Cenv.sup (scondpat expected_c sc1) (scondpat expected_c sc2)
    | Econdon(sc1, e) ->
       exp_before_on_c expected_k env e expected_c;
       scondpat expected_c sc1
    | Econdexp(e) ->
       exp_before_on_c expected_k env e expected_c; Env.empty
    | Econdpat(e, p) ->
       exp_before_on_c expected_k env e expected_c;
       let ty = Causal.skeleton_on_c expected_c p.p_typ in
       Cenv.make expected_k (pattern p ty) in
  let expected_c = Causal.new_var () in
  expected_c, scondpat expected_c sc

let implementation ff { desc = desc } =
  try
    match desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(f, _, e) ->
       Misc.push_binding_level ();
       let tc = exp Deftypes.Tany Env.empty e in
       Misc.pop_binding_level ();
       let tcs = generalise tc in
       Global.set_causality (Modules.find_value (Lident.Name(f))) tcs;
       (* output the signature *)
       if !Misc.print_causality then Pcaus.declaration ff f tcs
    | Efundecl (f, { f_kind = k; f_atomic = atomic;
		     f_args = pat_list; f_body = e; f_env = h0 }) ->
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
       let env =
         List.fold_left2
	   (fun acc p ty -> Env.append (Cenv.make expected_k (pattern p ty)) acc)
           Env.empty pat_list tc_arg_list in
       exp_before expected_k env e tc_res;
       Misc.pop_binding_level ();
       let tcs = generalise (Causal.funtype_list tc_arg_list tc_res) in
       (* then add the current entries in the global environment *)
       Global.set_causality (Modules.find_value (Lident.Name(f))) tcs;
       (* output the signature *)
       if !Misc.print_causality then Pcaus.declaration ff f tcs
  with
  | Error(loc, env, err) -> message loc env err

let implementation_list ff impl_list =
  List.iter (implementation ff) impl_list;
  impl_list
