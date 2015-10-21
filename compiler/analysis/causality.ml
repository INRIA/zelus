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

(* The relation c1 < c2 means that c1 must be computed before c2 *)
(* The causality analysis imposes extra constraints so that control-structures *)
(* are not opened. This could evolve if code-generation is changed. *)
(* Extra rules are: *)
(* 1. for a sequence of declarations, the sequential order is preserved. *)
(*    [let x1 = e1 in let x2 = e2 in do x = e] *)
(*    - x1: t1, x2: t2, x: t => t1 < t2 < t *)
(* 2. for a control-structure, [if x then do x1 = e1 and x2 = e2 done *)
(*                              else do x1 = e'1 and x2 = e'2 done *)
(*    - x: t[d] *)
(*    - [x1: t1[a]; x2: t2[b] ] < [x1: t1'[d]; x2: t2'[d]] with a, b, c < d *)
 (* 3. The same rule applies for all control-structures (present/automata) *)

let print x = Misc.internal_error "unbound" Printer.name x

open Misc
open Ident
open Global
open Zelus
open Location
open Defcaus
open Pcaus
open Causal

(* The typing environment for causality *)
module Cenv =
struct
  type t =
    | Empty
    | Append of Defcaus.tentry Ident.Env.t * t
    | On of t * Defcaus.t

  (* returns the type associated to [x] in [cenv] *)
  let rec find is_after x cenv =
    match cenv with
      | Empty -> raise Not_found
      | On(cenv, c) ->
        let ({ t_typ = ty } as tentry) = find is_after x cenv in
        { tentry with t_typ = if is_after then Causal.after ty c else ty }
      | Append(env, cenv) ->
        try
          Ident.Env.find x env
        with
        | Not_found -> find is_after x cenv

  let root x cenv = find false x cenv
  let find x cenv = find true x cenv

  (* the dependence introduced by a control block *)
  let rec dep = function
    | Empty -> Causal.new_var ()
    | On(_, c) -> c
    | Append(env, cenv) -> dep cenv
			       
  (* add a dependence from the current control block to a type [ty] *)
  let rec control cenv ty =
    let c = dep cenv in
    Causal.control c ty
  
  let empty = Empty
  let append env cenv = Append(env, cenv)
  let rec on cenv c = On(cenv, Causal.afterc (dep cenv) c)

  (* makes a copy of an environment for a set of names *)
  (* according to a boolean flag [is_last] *)
  let add_roots is_last dv cenv acc =
    Ident.S.fold
      (fun x acc ->
        Env.add x { (root x cenv) with t_last = is_last } acc) dv acc

  (* returns the environment for names in [defnames]. A variable *)
  (* [x in defnames] cannot be accessed with [last x] unless [x] is a *)
  (* continuous state variable *)
  let current cenv
      { Deftypes.dv = dv; Deftypes.di = di; Deftypes.der = dr } =
    let env = add_roots false dv cenv Env.empty in
    let env = add_roots false di cenv env in
    append (add_roots true dr cenv env) cenv

  (* returns the environment for names in [defnames]. All variable names *)
  (* can be accessed with a last *)
  let last cenv { Deftypes.dv = dv; Deftypes.di = di; Deftypes.der = dr } =
    let env = add_roots true dv cenv Env.empty in
    let env = add_roots true di cenv env in
    append (add_roots true dr cenv env) cenv

  let print_env ff cenv =
    (* print a typing environment *)
    let p_env ff l_env =
      let vars_env env =
        Env.fold (fun _ { t_typ = tc } acc -> Causal.vars acc tc) env [] in
      let env ff l_env =
        Env.iter
          (fun n { t_typ = ty; t_last = is_last } ->
           Format.fprintf ff "@[%s%a : %a@ @]" (if is_last then "last " else "")
                          Printer.name n (typ 0) ty) l_env in
      if not (Env.is_empty l_env)
      then let v_list = vars_env l_env in
           Format.fprintf ff "@[%a@ with %a@]" env l_env relation v_list in
    let rec print_env ff = function
      | Empty -> ()
      | On(cenv, c) ->
         Format.fprintf ff "@[%a on@ %a@]" print_env cenv Pcaus.caus c
      | Append(env, cenv) ->
         Format.fprintf ff "@[%a %a@]" print_env cenv p_env env in
    print_env ff cenv
end


(* Main error message *)
type error =
  | Eloop of Defcaus.t list
  (* dependence cycle and the current typing environment *)
  | Elast_in_continuous

exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin match kind with
        | Eloop(l) ->
           Format.eprintf "@[%aCausality error: this expression \
                           may instantaneously depend on itself.@.\
                           Here is an example of a cycle:@.@[%a@]@.@]"
                          output_location loc
                          Pcaus.cycle l
        | Elast_in_continuous ->
           Format.eprintf "%aCausality error: last is only allowed here \
                           for a variable defined by its derivative.@."
                          output_location loc
  end;
  raise Misc.Error

(* Unification and sub-typing relation *)

(** Typing a pattern. It returns an environment *)
let rec pattern ({ p_desc = desc; p_loc = loc } as p) ty =
  try
    let env = match desc with
      | Ewildpat | Econstpat _ | Econstr0pat _ -> Env.empty
      | Evarpat(x) ->
         Env.singleton x { t_typ = Causal.mark_with_name x ty; t_last = false }
      | Etuplepat(pat_list) ->
         let ty_list = Causal.filter_product (List.length pat_list) ty in
         append_list (List.map2 pattern pat_list ty_list)
      | Erecordpat(l) ->
         let c = Causal.new_var () in
         Causal.synchronise c ty;
         append_list (List.map (fun (_, p) -> pattern p (Causal.atom c)) l)
      | Etypeconstraintpat(p, _) -> pattern p ty
      | Eorpat(p, _) ->
         pattern p ty
      | Ealiaspat(p, n) ->
         append_list [pattern p ty;
                      Env.singleton n { t_typ = Causal.mark_with_name n ty;
                                        t_last = false }] in
    (* annotate the patter with causality information *)
    p.p_caus <- Causal.vars [] ty;
    env
  with
  | Causal.Unify(l) -> error loc (Eloop(l))

(** Build an environment from a typing environment *)
(* In a continuous context, [last x] is allowed for continuous state variables *)
let build_env l_env =
   let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } acc =
     let ty_c = Causal.skeleton_with_name n ty in
     let is_last =
       match sort with
         | Deftypes.Smem { Deftypes.m_kind = Some(Deftypes.Cont) } -> true
         | _ -> false in
     Env.add n { t_typ = ty_c; t_last = is_last } acc in
   Env.fold entry l_env Env.empty

(** Causality analysis of a match handler.*)
let match_handlers body expected_k env m_h_list =
  let handler { m_pat = p; m_body = b } =
    let c_e = Causal.new_var () in
    let m_env = pattern p (skeleton_on_c c_e p.p_typ) in
    let env = Cenv.append m_env env in
    body expected_k env b in
  List.map handler m_h_list

(** Causality analysis of a present handler *)
let present_handlers scondpat body expected_k env p_h_list h_opt =
  let handler { p_cond = scpat; p_body = b } =
    let _, new_env = scondpat expected_k env scpat in
    let env = Cenv.append new_env env in
    body (Types.lift_to_discrete expected_k) env b in
  let ty_list = List.map handler p_h_list in
  match h_opt with
    | None -> ty_list | Some(h) -> (body expected_k env h) :: ty_list

(* causality for [last x] *)
let last loc expected_k is_last ty =
  (* [last x] breaks an algebraic cycle *)
  (* it can be used in any discrete context or if [is_last = true] *)
  match expected_k with
    | Deftypes.Tdiscrete(true) -> Causal.last ty
    | _ -> if is_last then Causal.last ty else error loc Elast_in_continuous

(** causality of an expression *)
let rec exp expected_k env ({ e_desc = desc; e_typ = ty; e_loc = loc } as e) =
  try
    let tc = match desc with
      (* if variables from [env] are computed before [c] *)
      (* constants are synchronized with [c] *)
      | Econst _ | Econstr0 _
      | Eglobal _ | Eperiod _ -> Causal.skeleton ty
      | Elocal(x) ->
         begin try
             let { t_typ = actual_ty } = Cenv.find x env in
             (* subtyping must be done at an instanciation point *)
             let expected_ty = Causal.skeleton_with_name x ty in
             Causal.type_before_type actual_ty expected_ty; expected_ty
           with | Not_found -> print x
         end
      | Elast(x) ->
         begin try
             let { t_typ = ty1; t_last = is_last } =
               Cenv.root x env in last loc expected_k is_last ty1
           with | Not_found -> assert false
         end
      | Etuple(e_list) ->
         product (List.map (exp expected_k env) e_list)
      | Eapp(op, e_list) ->
         apply expected_k env op ty e_list
      | Erecord_access(e_record, _) ->
         let c = Causal.new_var () in
         exp_before_on_c expected_k env e_record c;
         Causal.skeleton_on_c c ty
      | Erecord(l) ->
         let c = Causal.new_var () in
         List.iter (fun (_, e) -> exp_before_on_c expected_k env e c) l;
         Causal.skeleton_on_c c ty
      | Etypeconstraint(e, _) -> exp expected_k env e
      | Elet(l, e_let) ->
         let new_env = local expected_k env l in
         let ty = exp expected_k (Cenv.append new_env env) e_let in
         ty
      | Eseq(e1, e2) ->
         let c = Causal.new_var () in
         exp_before_on_c expected_k env e1 c;
         exp_before_on_c expected_k env e2 c;
         Causal.skeleton_on_c c e2.e_typ
      | Epresent(h_e_list, e_opt) ->
         let c_e = Causal.new_var () in
         present_handler_exp_list expected_k (Cenv.on env c_e) h_e_list e_opt
      | Ematch(_, e, h_e_list) ->
         let c_e = Causal.new_var () in
         exp_before_on_c expected_k env e c_e;
         match_handler_exp_list expected_k (Cenv.on env c_e) h_e_list in
    (* annotate [e] with causality variables *)
    e.e_caus <- Causal.vars [] tc;
    tc
  with
  | Causal.Unify(l) -> error loc (Eloop(l))

(** Typing an application *)
and apply expected_k env op ty e_list =
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
    | (Einitial | Eup | Etest | Edisc), e_list ->
        List.iter
          (fun e ->
            exp_before_on_c expected_k env e c) e_list;
        Causal.skeleton_on_c c ty
    | Eop(_, lname), e_list ->
        let { info = info } = Modules.find_value lname in
        let ty_arg_list, ty_res = Causal.instance info in
        List.iter2 (exp_before expected_k env) e_list ty_arg_list;
        ty_res
    | Eevery(_, lname), e :: e_list ->
        let { info = info } = Modules.find_value lname in
        let ty_arg_list, ty_res = Causal.instance info in
        List.iter2 (exp_before expected_k env) e_list ty_arg_list;
        exp_before_on_c expected_k env e c;
        Causal.type_before_type (Causal.skeleton_on_c c ty) ty_res;
        ty_res
    | _ -> assert false

and exp_before_on_c expected_k env e expected_c =
  try
    let actual_ty = exp expected_k env e in
    let expected_ty = Causal.skeleton_on_c expected_c e.e_typ in
    Causal.type_before_type actual_ty expected_ty;
    (* annotate [e] with causality variables *)
    e.e_caus <- Causal.vars [] expected_ty
  with
  | Causal.Unify(l) -> error e.e_loc (Eloop(l))

and exp_before expected_k env e expected_ty =
  try
    let actual_ty = exp expected_k env e in
    Causal.type_before_type actual_ty expected_ty;
    (* annotate [e] with causality variables *)
    e.e_caus <- Causal.vars [] expected_ty
  with
  | Causal.Unify(l) -> error e.e_loc (Eloop(l))

(** Checking equations *)
and equation_list expected_k env eq_list =
  (* type the set of equations *)
  let new_env =
    List.fold_left
      (fun acc_env eq -> Causal.supenv (equation expected_k env eq) acc_env)
      Env.empty eq_list in
  new_env

and equation expected_k env
    { eq_desc = desc; eq_write = defnames; eq_loc = loc } =
  match desc with
    | EQeq(p, e) ->
        let ty_e = exp expected_k env e in
        pattern p (Cenv.control env ty_e)
    | EQpluseq(n, e) ->
        let ty_e = exp expected_k env e in
	Env.singleton n { t_typ = ty_e; t_last = false }
    | EQder(n, e, e0_opt, h_e_list) ->
        (* no causality constraint for [e] *)
        let _ = exp expected_k env e in
        let c_e = Causal.new_var () in
        let env = Cenv.on env c_e in
        (* type the initialization and handler *)
        let ty =
          match h_e_list with
          | [] -> Causal.skeleton_on_c c_e e.e_typ
          | _ -> let ty = present_handler_exp_list expected_k env h_e_list None in
		 Cenv.control env ty in
        let ty =
          match e0_opt with
          | None -> ty
          | Some(e0) ->
             Causal.sup ty (exp (Types.lift_to_discrete expected_k) env e0) in
        Env.singleton n { t_typ = ty; t_last = true }
    | EQinit(n, e0) ->
        let ty = exp expected_k env e0 in
        Env.singleton n { t_typ = Cenv.control env ty; t_last = false }
    | EQnext(n, e, e0_opt) ->
        ignore (exp expected_k env e);
        let expected_ty = Causal.skeleton_on_c (Causal.new_var ()) e.e_typ in
        begin match e0_opt with
              | None -> () | Some(e0) -> exp_before expected_k env e0 expected_ty
        end;
        Env.singleton n { t_typ = expected_ty; t_last = false }
    | EQautomaton(is_weak, s_h_list, se_opt) ->
        (* Typing a state expression *)
        let state env { desc = desc } =
          let c = Causal.new_var () in
          match desc with
            | Estate0 _ -> ()
            | Estate1(_, e_list) ->
               List.iter
                 (fun e -> exp_before_on_c expected_k env e c) e_list in
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
            let env = Cenv.append new_env (Cenv.on env c_e) in
            let env, shared_env =
              match b_opt with
              | None -> env, Env.empty
              | Some(b) ->
                block_eq_list_with_local_env
                  (Types.lift_to_discrete expected_k) env b in
            state (Cenv.append shared_env env) ns;
            shared_env in
          let s_env = build_env s_env in
          let env = Cenv.append s_env env in
          if is_weak then
            let env, shared_env =
              block_eq_list_with_local_env expected_k env b in
            let env = Cenv.append shared_env env in
            let trans_env =
              Causal.supenv_list (List.map (escape env) trans) in
            Env.append shared_env trans_env
          else
            let trans_env =
              Causal.supenv_list (List.map (escape env) trans) in
            let shared_env = block_eq_list expected_k env b in
            Env.append shared_env trans_env in
        (* all variables read in [s_h_list] must be scheduled before *)
        (* a certain date *)
        let env = Cenv.on env (Causal.new_var ()) in
        (* a shared variable [x] defined in [s_h_list] can potentially *)
        (* be accessed with [last x] *)
        let env = Cenv.last env defnames in
        let new_env =
          supenv_list (List.map (handler expected_k env) s_h_list) in
        ignore (Misc.optional_map (state env) se_opt);
        new_env
    | EQmatch(_, e, m_h_list) ->
       let c_e = Causal.new_var () in
       exp_before_on_c expected_k env e c_e;
       (* all variables read in [m_h_list] must be scheduled before the *)
       (* date [e] is scheduled *)
       let env = Cenv.on env c_e in
       (* a shared variable [x] defined in [m_h_list] can potentially *)
       (* be accessed with [last x] *)
       let env = Cenv.last env defnames in
       match_handler_block_eq_list expected_k env m_h_list
    | EQpresent(p_h_list, b_opt) ->
      (* all variables read in [p_h_list] must be scheduled *)
      (* before a certain date *)
      let c_e = Causal.new_var () in
      let env = Cenv.on env c_e in
      (* a shared variable [x] defined in [p_h_list] can potentially *)
      (* be accessed with [last x] *)
      let env = Cenv.last env defnames in
       present_handler_block_eq_list expected_k env p_h_list b_opt
    | EQreset(eq_list, e) ->
        (* variables defined in [b] depend on [e] *)
       let c_e = Causal.new_var () in
       exp_before_on_c expected_k env e c_e;
       equation_list expected_k env eq_list
    | EQemit(n, e_opt) ->
        let c_e = Causal.new_var () in
        begin match e_opt with
          | None -> ()
          | Some(e) -> exp_before_on_c expected_k env e c_e
        end;
        Env.singleton n { t_typ = Cenv.control env (atom c_e); t_last = false }
    | EQblock(b_eq_list) ->
        block_eq_list expected_k env b_eq_list

(* Typing a present handler for expressions *)
(* The handler list is not be empty *)
and present_handler_exp_list expected_k env p_h_list e_opt =
  let ty_list = present_handlers scondpat exp expected_k env p_h_list e_opt in
  Causal.sup_list ty_list

(* Typing a present handler for blocks *)
and present_handler_block_eq_list expected_k env p_h_list p_h_opt =
  let env_list =
    present_handlers scondpat block_eq_list expected_k env p_h_list p_h_opt in
  Causal.supenv_list env_list

(* Typing a match handler for expressions *)
(* The handler list is not empty *)
and match_handler_exp_list expected_k env m_h_list =
  let ty_list = match_handlers exp expected_k env m_h_list in
  Causal.sup_list ty_list

(* Typing a match handler for blocks *)
and match_handler_block_eq_list expected_k env m_h_list =
  let new_env_list = match_handlers block_eq_list expected_k env m_h_list in
  Causal.supenv_list new_env_list

(* Typing a block with a set of equations in its body. Returns *)
(* the pair [env, shared_env] *)
(* [env] is the environment of variable defined globally plus local variables *)
(* [shared_env] is the variables between the [do ... done] *)
(* [expected_k] is the expected kind for the body. *)
and block_eq_list_with_local_env expected_k env
    { b_locals = l_list; b_body = eq_list;
      b_env = b_env; b_loc = loc; b_write = defnames } =
  (* A block structure is scheduled as a whole. *)
  (* Introduce [c_e]: every computation which is not shared must be scheduled *)
  (* after [c_e] *)
  (* Local definitions must be executed before equations in the current block *)
  let c_e = Causal.new_var () in
  let local local_env l =
    let new_env = local expected_k local_env l in
    Cenv.append new_env local_env in
  let env = List.fold_left local (Cenv.on env c_e) l_list in
  (* Build the typing environment for names introduced by a *)
  (* [local x1,..., xn in ...] *)
  let b_env = build_env b_env in
  let env = Cenv.append b_env env in
  (* Then, type the body *)
  (* Copy shared variables, that is, names in [defnames] *)
  (* so that they do not have to be scheduled before [c_e] *)
  let env = Cenv.current env defnames in
  try
    let new_env = equation_list expected_k env eq_list in
    (* detect causality cycles inside the block *)
    let shared_env = Causal.env_structurally_before_env new_env b_env in
    env, shared_env
  with Causal.Unify(l) -> error loc (Eloop(l))

(* Typing a block with a set of equations in its body. Only returns *)
(* the environment of shared variables *)
and block_eq_list expected_k env b =
  let _, shared_env = block_eq_list_with_local_env expected_k env b in
  shared_env

(* Typing a local declaration. Returns the environment of local variables *)
and local expected_k env { l_eq = eq_list; l_env = l_env; l_loc = loc } =
  (* First extend the typing environment *)
  let l_env = build_env l_env in
  let env = Cenv.append l_env env in
  (* Then type the body *)
  try
    let new_env = equation_list expected_k env eq_list in
    ignore (Causal.env_structurally_before_env new_env l_env);
    l_env
  with Causal.Unify(l) -> error loc (Eloop(l))

(* Typing  a signal pattern. *)
and scondpat expected_k env sc =
  let rec scondpat c { desc = desc; loc = loc } =
    match desc with
    | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
        Causal.supenv (scondpat c sc1) (scondpat c sc2)
    | Econdon(sc1, e) ->
      exp_before_on_c expected_k env e c;
      scondpat c sc1
    | Econdexp(e) ->
      exp_before_on_c expected_k env e c; Env.empty
    | Econdpat(e, p) ->
      exp_before_on_c expected_k env e c;
      let ty = Causal.skeleton_on_c c p.p_typ in
      pattern p ty in
  let c = Causal.new_var () in
  c, scondpat c sc

let implementation ff { desc = desc } =
  try
    match desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(_, e) ->
       Misc.push_binding_level ();
       ignore (exp Deftypes.Tany Cenv.empty e);
       Misc.pop_binding_level ()
    | Efundecl (f, { f_kind = k; f_atomic = atomic; f_args = pat_list;
                     f_body = e; f_env = h0 }) ->
       Misc.push_binding_level ();
       let expected_k = Interface.kindtype k in
       (* first type the body *)
       let c_in = Causal.new_var () in
       let c_res = Causal.new_var () in
       ignore (Causal.afterc c_in c_res);
       let ty_arg_list, ty_res =
         (* for an atomic node, all outputs depend on all inputs *)
         if atomic then
           List.map (fun p -> Causal.skeleton_on_c c_in p.p_typ) pat_list,
           Causal.skeleton_on_c c_res e.e_typ
         else
           List.map (fun p -> Causal.skeleton_on_c (Causal.new_var ()) p.p_typ)
                    pat_list,
           Causal.skeleton e.e_typ in
       let env =
         List.fold_left2 (fun acc p ty -> Env.append (pattern p ty) acc)
                         Env.empty pat_list ty_arg_list in
       exp_before expected_k (Cenv.append env Cenv.empty) e ty_res;
       Misc.pop_binding_level ();
       let tys = generalise ty_arg_list ty_res in
       (* then add the current entries in the global environment *)
       Global.set_causality (Modules.find_value (Lident.Name(f))) tys;
       (* output the signature *)
       if !Misc.print_causality then Pcaus.declaration ff f tys
  with
  | Error(loc, err) -> message loc err

let implementation_list ff impl_list = List.iter (implementation ff) impl_list
