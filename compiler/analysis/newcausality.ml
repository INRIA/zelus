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
(* causality check *)

(* The relation c1 < c2 means that c1 must be computed before c2 *)
(* In a sequence of local declarations *)
(* let x1 = e1 in let x2 = e2 in do x = e done *)
(* (x1 < x2) & (x2 < x) *)
(* E.g., equations like let y = x in let z = 1 in do ... done *)
 
open Misc
open Ident
open Global
open Zelus
open Location
open Defcaus
open Newcausal

(* Main error message *)
type error =
  | Eloop of Defcaus.info list
  | Elast_in_continuous

exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin match kind with
	| Eloop(l) ->
	   Format.eprintf "%aCausality error: this expression \
			   may instantaneously depend on itself.@."
			  output_location loc;
	   Format.eprintf "%a" Printer.cycle l
	| Elast_in_continuous ->
	   Format.eprintf "%aCausality error: the left limit is only allowed \
                           for a variable defined by its derivative.@."
			  output_location loc
  end;
  raise Misc.Error

(* Unification and sub-typing relation *)
let unify loc actual_ty expected_ty =
  try
    Newcausal.unify actual_ty expected_ty
  with
    | Newcausal.Unify(l) -> error loc (Eloop(l))

let less_than loc actual_ty expected_ty =
  try
    Newcausal.less actual_ty expected_ty
  with
    | Newcausal.Unify(l) -> error loc (Eloop(l))

let synchronise loc c actual_ty =
  try
    Newcausal.synchronise c actual_ty
  with
    | Newcausal.Unify(l) -> error loc (Eloop(l))

(** Build an environment from a typing environment *)
(** all defined variables from [l_env] must be done after [c_before] *)
(** and before [c_after] *)
let build_env c_before c_after l_env env =
  let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } = 
    let ty_c = Newcausal.skeleton n ty in
    Newcausal.less (Newcausal.skeleton_on_c c_before ty) ty_c;
    Newcausal.less ty_c (Newcausal.skeleton_on_c c_after ty);
    let is_der =
      match sort with
	| Deftypes.Mem { Deftypes.t_der_is_defined = is_der } -> is_der
	| _ -> false in
    let is_next =
      match sort with
	| Deftypes.Mem { Deftypes.t_next_is_set = is_next } -> is_next
	| _ -> false in
    { t_typ = ty_c; t_der = is_der; t_next = is_next } in
  Env.fold (fun n tentry acc -> Env.add n (entry n tentry) acc) l_env env

(* Build a copy of the environment for the shared variables modified in the *)
(* current block. All types must be greater that [c_before] *)
let copy_shared_variables env c_before
    { Deftypes.dv = dv; Deftypes.di = di; Deftypes.dr = dr } =
  let shared n (acc, n_old_ty_new_ty_list) =
    let ({ t_typ = old_ty; t_next = is_next } as entry ) =
      try Env.find n env with Not_found -> assert false in
    let c = Newcausal.new_var () in
    cless c_before c;
    if is_next then acc, n_old_ty_new_ty_list
    else
      let new_ty = copy_on_c c old_ty in
      Env.add n { entry with t_typ = new_ty } acc, 
      (n, old_ty, new_ty) :: n_old_ty_new_ty_list in
  (* the list of triples (n, old_ty, new_ty) contains names from [dv] and [di] *)
  (* but not [dv] *)
  let env, n_old_ty_new_ty_list = Ident.S.fold shared dv (env, []) in
  Ident.S.fold shared di (env, n_old_ty_new_ty_list)

(* Synchronize types. For every element [(n, old_ty, new_ty)] of the list *)
(* [n_old_ty_new_ty_list], apply [new_ty < old_ty] and synchronise *)
(* [old_ty] with [c] *)
let synchronise_shared_variables loc c_before old_ty_new_ty_list =
  let c = Newcausal.new_var () in
  Newcausal.cless c_before c;
  let synchronise (n, old_ty, new_ty) =
    less_than loc new_ty old_ty;
    synchronise loc c old_ty in
  List.iter synchronise old_ty_new_ty_list

let rec pattern expected_k env { p_desc = desc; p_loc = loc; p_typ = ty } =
  match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> 
        Newcausal.skeleton_on_c (Newcausal.new_var ()) ty
    | Evarpat(x) -> 
        begin try let { t_typ = ty1 } = Env.find x env in ty1 
	  with | Not_found -> assert false end
    | Etuplepat(pat_list) ->
        product (List.map (pattern expected_k env) pat_list)
    | Erecordpat(l) -> 
        let pattern_less_than_on_c pat c =
          let actual_ty = pattern expected_k env pat in
          less_than loc actual_ty (Newcausal.skeleton_on_c c pat.p_typ) in
        let c = Newcausal.new_var () in
        List.iter (fun (_, p) -> pattern_less_than_on_c p c) l;
        Newcausal.skeleton_on_c c ty
    | Etypeconstraintpat(p, _) -> pattern expected_k env p
    | Eorpat(p1, p2) -> 
        let ty1 = pattern expected_k env p1 in
        let ty2 = pattern expected_k env p2 in
        unify p1.p_loc ty1 ty2;
        ty1
    | Ealiaspat(p, n) -> 
        let ty_p = pattern expected_k env p in
        let { t_typ = ty_n } = 
	  try Env.find n env with | Not_found -> assert false in
	unify p.p_loc ty_p ty_n;
        ty_p
	
(** Causality analysis of a match handler.*)
(* All computations of the body must be done after [c_before] *)
(* and after [c_after] *)
let match_handlers body expected_k c_before c_after env m_h_list =
  let handler { m_body = b; m_env = m_env } =
    let c_between = Newcausal.new_var () in
    cless c_before c_between; cless c_between c_after;
    let env = build_env c_before c_between m_env env in
    body expected_k c_between c_after env b in
  List.iter handler m_h_list

(** Causality analysis of a present handler *)
let present_handlers scondpat body expected_k c_before c_after env p_h_list =
  let handler { p_cond = scpat; p_body = b; p_env = p_env } =
    let c_between = Newcausal.new_var () in
    cless c_before c_between; cless c_between c_after;
    let env = build_env c_before c_between p_env env in
    scondpat expected_k c_between env scpat;
    body (Types.lift_to_discrete expected_k) c_between c_after env b in
  List.iter handler p_h_list


(** Causality analysis of a block. *)
(* for shared variables [x1:old_t1,...,xn:old_tn] *)
(* first build a copy environment [x1:new_t1,...,xn:new_tn]  then type the block *)
(* at the end, synchronise all the types that have been computed *)
(* That is: [new_t1 < old_t1,..., new_tn < old_tn] and all types [old_ti] *)
(* must synchronise with each others *)
let block locals body expected_k c_before c_after env 
    { b_locals = l_list; b_body = bo; b_env = b_env; b_write = w; b_loc = loc } =
  (* Build the typing environment *)
  let c_between = Newcausal.new_var () in
  cless c_before c_between; cless c_between c_after;
  (* build a local copy of the global environment for *)
  (* shared variables of the block *)
  let env, old_ty_new_ty_list = copy_shared_variables env c_between w in
  (* local variables [local x1,...,xn in ...] must be computed after [c_after] *)
  let env = build_env c_before c_between b_env env in
  (* local definitions must be executed before equations in the current block *)
  let env = locals expected_k c_before c_between env l_list in
  (* Then, type the body *)
  body expected_k c_between c_after env bo;
  (* shared variables written in the block must be computed after [c_after] *)
  (* and all shared variables must synchronise with some [c] *)
  synchronise_shared_variables loc c_between old_ty_new_ty_list;
  env 

(* causality for [last x] *)
let last loc expected_k is_der ty =
  (* [last x] breaks an algebraic cycle only in a discrete context *)
  (* or [x] is defined by a derivative [der x = ...] *)
  match expected_k with 
    | Deftypes.Tdiscrete(true) -> Newcausal.last ty 
    | _ -> if is_der then Newcausal.last ty
           else error loc Elast_in_continuous

(** causality of an expression *)
let rec exp expected_k env { e_desc = desc; e_typ = ty; e_loc = loc } =
  match desc with
    | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> 
        Newcausal.skeleton_on_c (Newcausal.new_var ()) ty
    | Elocal(x) -> 
        begin try 
	  let { t_typ = actual_ty } = Env.find x env in 
	  (* subtyping is done at instanciation points only *)
	  let expected_ty = Newcausal.skeleton x ty in
	  less_than loc actual_ty expected_ty; expected_ty
          with | Not_found -> assert false
        end
    | Elast(x) -> 
        begin try 
	  let { t_typ = ty1; t_der = der } = 
	    Env.find x env in last loc expected_k der ty1
	  with | Not_found -> assert false
	end
    | Etuple(e_list) -> 
        product (List.map (exp expected_k env) e_list)
    | Eapp(op, e_list) -> 
        apply expected_k env op ty e_list
    | Erecord_access(e_record, _) -> 
        let c = Newcausal.new_var () in
	exp_less_than_on_c expected_k env e_record c;
        Newcausal.skeleton_on_c c ty
    | Erecord(l) -> 
        let c = Newcausal.new_var () in
        List.iter (fun (_, e) -> exp_less_than_on_c expected_k env e c) l;
        Newcausal.skeleton_on_c c ty
    | Etypeconstraint(e, _) -> exp expected_k env e
    | Elet(l, e_let) -> 
        let c_before = Newcausal.new_var () in
        let c_after = Newcausal.new_var () in
        let env = local expected_k c_before c_after env l in
        exp expected_k env e_let
    | Eseq(e1, e2) -> 
        ignore (exp expected_k env e1);
        exp expected_k env e2
    | Epresent(h_e_list, e_opt) ->
        let c_res = Newcausal.new_var () in
	let ty_res = Newcausal.skeleton_on_c c_res ty in
        let _ =
	  Misc.optional_map 
	    (fun e -> exp_less_than_on_c expected_k env e c_res) e_opt in
	present_handler_exp_list expected_k c_res env h_e_list;
	ty_res
    | Ematch(_, e, h_e_list) ->
        let c_before = Newcausal.new_var () in
	let c_res = Newcausal.new_var () in
	exp_less_than_on_c expected_k env e c_before;
	let ty_res = Newcausal.skeleton_on_c c_res ty in
        match_handler_exp_list expected_k c_before c_res env h_e_list;
	ty_res
    
(** Typing an application *)
and apply expected_k env op ty e_list =
  let c = Newcausal.new_var () in
  match op, e_list with
    | Eunarypre, [e] -> 
        exp_less_than_on_c expected_k env e (Newcausal.new_var ());
        Newcausal.skeleton_on_c c ty
    | Efby, [e1;e2] ->
        exp_less_than_on_c expected_k env e2 (Newcausal.new_var ());
        exp_less_than_on_c expected_k env e1 c;
	Newcausal.skeleton_on_c c ty
    | Eminusgreater, [e1;e2] ->
        exp_less_than_on_c expected_k env e1 c;
        exp_less_than_on_c expected_k env e2 c;
	Newcausal.skeleton_on_c c ty
    | Eifthenelse, [e1; e2; e3] ->
        exp_less_than_on_c expected_k env e1 c;
        exp_less_than_on_c expected_k env e2 c;
        exp_less_than_on_c expected_k env e3 c;
        Newcausal.skeleton_on_c c ty
    | (Einitial | Eup | Etest | Edisc | Eon), e_list ->
        List.iter 
	  (fun e -> 
	    exp_less_than_on_c expected_k env e c) e_list;
        Newcausal.skeleton_on_c c ty
    | Eop(lname), e_list ->
        let { info = info } = Modules.find_value lname in
	let ty_arg_list, ty_res = Newcausal.instance info in
	List.iter2 (exp_less_than expected_k env) e_list ty_arg_list;
        ty_res
    | Eevery(lname), e :: e_list ->
        let { info = info } = Modules.find_value lname in
	let ty_arg_list, ty_res = Newcausal.instance info in
	List.iter2 (exp_less_than expected_k env) e_list ty_arg_list;
        exp_less_than_on_c expected_k env e c;
	less_than e.e_loc (Newcausal.skeleton_on_c c ty) ty_res;
	ty_res
    | _ -> assert false

and exp_less_than_on_c expected_k env e expected_c =
  let actual_ty = exp expected_k env e in
  less_than e.e_loc actual_ty (Newcausal.skeleton_on_c expected_c e.e_typ)

and exp_less_than expected_k env e expected_ty =
  let actual_ty = exp expected_k env e in
  less_than e.e_loc actual_ty expected_ty

and exp_expect_on_c expected_k env e expected_c =
  let actual_ty = exp expected_k env e in
  unify e.e_loc actual_ty (Newcausal.skeleton_on_c expected_c e.e_typ)

and exp_less_than_opt expected_k env e_opt expected_ty =
  match e_opt with
  | None -> () | Some(e) -> exp_less_than expected_k env e expected_ty

(** Checking equations *)
and equation_list expected_k env eq_list = 
  List.iter (equation expected_k env) eq_list

and equation expected_k env { eq_desc = desc; eq_loc = loc } =
  match desc with
    | EQeq(p, e) -> 
        let ty_p = pattern expected_k env p in
        exp_less_than expected_k env e ty_p
    | EQder(n, e, e0_opt, p_h_e_list) ->
        let { t_typ = ty_n } = 
	  try Env.find n env with | Not_found -> assert false in
        let c_res = Newcausal.new_var () in
	synchronise loc c_res ty_n;
	(* no causality constraint for [e] *)
	let _ = exp expected_k env e in
	exp_less_than_opt (Types.lift_to_discrete expected_k) env e0_opt ty_n;
	present_handler_exp_list expected_k c_res env p_h_e_list
    | EQinit(p, e0, e_opt) ->
        let ty_p = pattern expected_k env p in
        exp_less_than (Types.lift_to_discrete expected_k) env e0 ty_p;
        exp_less_than_opt expected_k env e_opt ty_p
    | EQnext(p, e, e0_opt) ->
        let ty_p = pattern expected_k env p in
        (* [p] does not depend on [e] *)
	let _ = exp expected_k env e in
        (* but [p] depends on [e0_opt] *)
	exp_less_than_opt (Types.lift_to_discrete expected_k) env e0_opt ty_p;
    | EQautomaton(s_h_list, se_opt) ->
        (* Typing a state expression.*)
        let state env { desc = desc } =
	  match desc with
	    | Estate0 _ -> ()
	    | Estate1(_, e_list) -> 
	        List.iter 
		  (fun e -> let c_after = Newcausal.new_var () in
			    exp_less_than_on_c expected_k env e c_after)
		  e_list in
	(* handler *)
        (* Scheduling is done this way: *)
	(* - compute unless conditions; if one is true, execute the handler *)
	(* - otherwise, compute the body; *)
	(* - then the until conditions and possibly escapes *)
	let handler expected_k env 
	      { s_body = b; s_until = until; s_unless = unless; s_env = s_env } =
          (* typing an escape. Conditions and actions must be executed after *)
	  (* [c_before]. Condition are done before [c_after_conditions]. *)
	  let escape c_before c_after_conditions env
	     { e_cond = sc; e_block = b_opt; e_next_state = ns; e_env = e_env } =
            let c_after = Newcausal.new_var () in
	    let env = build_env c_before c_after e_env env in
	    scondpat expected_k c_after_conditions env sc;
	    let env = 
	      match b_opt with 
	      | None -> env 
	      | Some(b) -> 
		 block_eq_list (Types.lift_to_discrete expected_k) 
			       c_after_conditions c_after env b in
	    state env ns in
          let c_before = Newcausal.new_var () in
          let c_after = Newcausal.new_var () in
          let env = build_env c_before c_after s_env env in
	  let c_after_unless = Newcausal.new_var () in
          let env = block_eq_list expected_k c_after_unless c_after env b in
          (* first execute unless statements *)
	  List.iter (escape c_before c_after_unless env) unless;
	  List.iter (escape c_after_unless c_after env) until;
        in
        List.iter (handler expected_k env) s_h_list;
	ignore (Misc.optional_map (state env) se_opt)
    | EQmatch(_, e, m_h_list) ->
        (* the main dependence variable for the control structure *)
        let c_before = Newcausal.new_var () in
        let c_after = Newcausal.new_var () in
        exp_less_than_on_c expected_k env e c_before;
        match_handler_block_eq_list expected_k c_before c_after env m_h_list
    | EQpresent(p_h_list, b_opt) ->
        (* the main dependence variable for the control structure *)
        let c_before = Newcausal.new_var () in
        let c_after = Newcausal.new_var () in
        let _ = 
	  Misc.optional_map 
	    (fun b -> block_eq_list expected_k c_before c_after env b) b_opt in
        present_handler_block_eq_list expected_k c_before c_after env p_h_list
    | EQreset(b, e) -> 
        (* the main dependence variable for the control structure *)
        let c_before = Newcausal.new_var () in
	let c_after = Newcausal.new_var () in
	exp_less_than_on_c expected_k env e c_before;
        ignore (block_eq_list expected_k c_before c_after env b)
    | EQemit(n, e_opt) ->
        let { t_typ = ty_n } = try Env.find n env with Not_found -> assert false in
	let c_res = Newcausal.new_var () in
	synchronise loc c_res ty_n;
	ignore
	  (Misc.optional_map 
	     (fun e -> exp_less_than_on_c expected_k env e c_res) e_opt)
	  
(* Typing a present handler. All computation from the block must *)
(* be done before [c_res] *)
and present_handler_exp_list expected_k c_res env p_h_list =
  present_handlers scondpat 
    (fun expected_k c_before c_after env e -> 
     exp_less_than_on_c expected_k env e c_after)
    expected_k (Newcausal.new_var ()) c_res env p_h_list

(* Typing a present handler. All computation from the block must be done after *)
(* [c_before] and before [c_after] *)
and present_handler_block_eq_list expected_k c_before c_after env p_h_list =
  present_handlers scondpat 
    (fun expected_k c_before c_after env b -> 
      ignore (block_eq_list expected_k c_before c_after env b))
    expected_k c_before c_after env p_h_list

(* Typing a match handler. All computation from the block must be done after *)
(* [c_before] and before [c_res] *)
and match_handler_exp_list expected_k c_before c_res env m_h_list =
  match_handlers
    (fun expected_k c_before c_after env e -> 
     exp_less_than_on_c expected_k env e c_after)
      expected_k c_before c_res env m_h_list

(* Typing a match handler. All computation from the block must be done after *)
(* [c_before] and after [c_after] *)
and match_handler_block_eq_list expected_k c_before c_after env m_h_list =
  match_handlers
    (fun expected_k c_before c_after env b -> 
      ignore (block_eq_list expected_k c_before c_after env b))
    expected_k c_before c_after env m_h_list

(* Typing a block. All computation from the block must be done after [c_before] *)
(* and before [c_after] *)
and block_eq_list expected_k c_before c_after env b =
  let locals expected_k c_before c_after env l_list =
    List.fold_left (local expected_k c_before c_after) env l_list in
  let equation_list expected_k c_before c_after env eq_list = 
    equation_list expected_k env eq_list in
  block locals equation_list expected_k c_before c_after env b

(* Typing a local declaration. All computation must be done after [c_before] *)
(* and before [c_after] *)
and local expected_k c_before c_after env 
    { l_eq = eq_list; l_loc = loc; l_env = l_env } =
  (* First extend the typing environment *)
  let env = build_env c_before c_after l_env env in
  (* then type the body *)
  List.iter (equation expected_k env) eq_list; env
           
(* Typing  a signal pattern. Every computation from [scpat] *)
(* must be done before [c_after] *)
and scondpat expected_k c_after env { desc = desc; loc = loc } =
  match desc with
    | Econdand(sc1, sc2) 
    | Econdor(sc1, sc2) -> 
       scondpat expected_k c_after env sc1; scondpat expected_k c_after env sc2
    | Econdon(sc1, e) ->
       scondpat expected_k c_after env sc1; 
       exp_less_than_on_c expected_k env e c_after
    | Econdexp(e) -> 
       exp_less_than_on_c expected_k env e c_after
    | Econdpat(e, p) -> 
       exp_less_than_on_c expected_k env e c_after;
       let ty_p = pattern expected_k env p in
       less_than loc ty_p (Newcausal.skeleton_on_c c_after p.p_typ) 

let implementation ff impl =
  try
    match impl.desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(_, e) -> 
       Misc.push_binding_level ();
       ignore (exp Deftypes.Tany Env.empty e);
       Misc.pop_binding_level ()
    | Efundecl
	(f, { f_kind = k; f_args = pat_list; f_body = e; f_env = h0 }) ->
       Misc.push_binding_level ();
       let expected_k = Interface.kindtype k in
       let env = 
	 build_env (Newcausal.new_var ()) (Newcausal.new_var ()) h0 Env.empty in
       (* first type the body *)
       let ty_arg_list = List.map (pattern expected_k env) pat_list in
       let ty_res = exp expected_k env e in
       Misc.pop_binding_level ();
       let tys = generalise ty_arg_list ty_res in
       (* then add the current entries in the global environment *)
       Global.set_causality (Modules.find_value (Lident.Name(f))) tys;
       (* output the signature *)
       if !Misc.print_causality then Printer.declaration ff f tys
  with
  | Error(loc, err) -> message loc err

let implementation_list ff impl_list = List.iter (implementation ff) impl_list
