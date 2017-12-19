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
(* may evolve if code-generation changes. *)
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

let print x = Misc.internal_error "unbound" Printer.name x

(* Main error message *)
type error =
  | Cless_than of tc * tc * Cenv.env * cycle (* not (expected_ty < actual_ty) *)
  | Ccycle of Ident.t * tc * Cenv.env * cycle (* contains a cycle *)
                    
(* dependence cycle and the current typing environment *)
exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin
    match kind with
    | Cless_than(left_tc, right_tc, env, cycle) ->
        (* computes the set of names that appear in [cycle] *)
        let cset_cycle = List.fold_left Causal.vars_c S.empty cycle in
        (* only keep entries in the environment with type variables *)
        (* that belong the [cset_cycle] *)
        let env = Cenv.clean cset_cycle env in
        (* keep only names in cycle that either appear in the types *)
        Causal.mark true left_tc;
        Causal.mark true right_tc;
        let left_tc = simplify true left_tc in
        let right_tc = simplify true right_tc in
        let cset = Causal.vars (Causal.vars S.empty left_tc) right_tc in
        let _ = Cenv.mark cset env in
        Cenv.shorten env;
        let env = Cenv.simplify env in
        let cset = Cenv.mark cset env in
        Cenv.shorten env;
        let cycle = Causal.shrink_cycle cset cycle in
        Format.eprintf
          "@[%aCausality error: This expression has causality type@ %a,@ \
           whereas it should be less than@ %a@.\
           Here is an example of a cycle:@.%a@.\
           in the current typing environment:@.%a@.@]"
          output_location loc
          Pcaus.ptype left_tc
          Pcaus.ptype right_tc
          Pcaus.cycle cycle
          (Causal.penv cset) env
    | Ccycle(n, tc, env, cycle) ->
        (* computes the set of names that appear in [cycle] *)
        let cset_cycle = List.fold_left Causal.vars_c S.empty cycle in
        (* only keep entries in the environment with type variables *)
        (* that belong the [cset_cycle] *)
        let env = Cenv.clean cset_cycle env in
        (* simplify types and environment *)
        Causal.mark true tc;
        let cset_tc = Causal.vars S.empty tc in
        let _ = Cenv.mark S.empty env in
        Cenv.shorten env;
        let env = Cenv.simplify env in
        let cset = Cenv.mark cset_tc env in
        Cenv.shorten env;
        let cycle = Causal.shrink_cycle cset cycle in
        (* keep only names in cycle that either appear in the type *)
        Format.eprintf
         "@[%aCausality error: The variable %a \
          cannot be given the causality type@,\
          %a@, because this would create a cycle in the current environment: @,\
          @[%a@]@.\
          Here is an example of a cycle:@.@[%a@]@.@]"
         output_location loc
         Printer.source_name n
         Pcaus.ptype tc
         (Causal.penv cset) env
         Pcaus.cycle cycle       
  end;
  raise Misc.Error

let less_than loc env actual_ty expected_ty =
  try
    Causal.less actual_ty expected_ty
  with
  | Causal.Clash(cycle) ->
      error loc (Cless_than(actual_ty, expected_ty, env, cycle))

let read loc x env =
  let path, ({ t_typ = tc } as tentry) = Cenv.find x env in
  try
    { tentry with t_typ = Cenv.before false path tc }
  with
  | Causal.Clash(cycle) -> error loc (Ccycle(x, tc, env, cycle))

let write loc x env =
  let path, ({ t_typ = tc } as tentry) = Cenv.find x env in
  try
    { tentry with t_typ = Cenv.before true path tc }
  with
  | Causal.Clash(cycle) -> error loc (Ccycle(x, tc, env, cycle))
                             
(** Typing a pattern. [pattern env p = ty] when [ty] is the type *)
(* of pattern [p] in [env] *)
let rec pattern env ({ p_desc = desc; p_loc = loc; p_typ = ty } as p) =
  let tc = match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ ->
        Causal.skeleton_on_c (Causal.new_var ()) ty
    | Evarpat(x) ->
        begin try let { t_typ = ty1 } = write loc x env in ty1
          with | Not_found -> print x 
        end
    | Etuplepat(pat_list) ->
        product(List.map (pattern env) pat_list)
    | Erecordpat(l) ->
        let pattern_less_than_on_c pat c =
          let actual_ty = pattern env pat in
          let expected_ty = Causal.skeleton_on_c c pat.p_typ in
          less_than loc env actual_ty expected_ty in
        let c = Causal.new_var () in
        List.iter (fun (_, p) -> pattern_less_than_on_c p c) l;
        Causal.skeleton_on_c c ty
    | Etypeconstraintpat(p, _) -> pattern env p
    | Eorpat(p1, p2) ->
        let ty1 = pattern env p1 in
        let ty2 = pattern env p2 in
        Causal.suptype true ty1 ty2
    | Ealiaspat(p, x) ->
        let ty_p = pattern env p in
        let ty_n =
          begin try let { t_typ = ty1 } = write loc x env in ty1
            with | Not_found -> print x 
          end in
        less_than p.p_loc env ty_n ty_p;
        ty_p in
  (* annotate the pattern with causality information *)
  p.p_caus <- S.elements (Causal.vars S.empty tc);
  tc
  
(** Build an environment from a typing environment. *)
let build_env l_env env =
  let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } acc =
    let cur_tc = Causal.annotate (Cname n) (Causal.skeleton ty) in
    let last_tc_opt =
      match sort with
      | Smem { m_previous = true } ->
          Some(Causal.annotate (Clast n) (Causal.skeleton ty))
      | _ -> None in
    Env.add n { t_typ = cur_tc; t_last_typ = last_tc_opt } acc in
  Cenv.append (Env.fold entry l_env Env.empty) env
    
(** Build an environment with all entries synchronised on [c] *)
let build_env_on_c c l_env env =
  let entry n { Deftypes.t_typ = ty; Deftypes.t_sort = sort } acc =
    let cur_tc = Causal.annotate (Cname n) (Causal.skeleton_on_c c ty) in
    let last_tc_opt =
      match sort with
      | Smem { m_previous = true } ->
          Some(Causal.annotate (Clast n) (Causal.skeleton_on_c c ty))
      | _ -> None in
    Env.add n { t_typ = cur_tc; t_last_typ = last_tc_opt } acc in
  Cenv.append (Env.fold entry l_env Env.empty) env

(** over constraint the causality so that a block is scheduled atomically *)
(* that is, as if all output would depend on all inputs (free variables) *)
(*
let atomic env ({ eq_write = { dv = dv } } as eq) =
  (* for every defined name [x1,...,xn] *)
  (* introduce an environment [x1:ct1[c1];...;xn:ctn[c1]] *)
  let new_env =
    S.fold
      (fun x acc ->
         let { t_typ = ty; t_last_typ = ty_last } = Env.find x env in
         Env.add x { t_typ = Causal.skeleton_on_c c()
*)
    
(** Causality analysis of a match handler.*)
let match_handlers body env m_h_list =
  let handler { m_pat = p; m_body = b; m_env = m_env } =
    let c = Causal.new_var () in
    let env = build_env_on_c c m_env env in
    let _ = pattern env p in
    (* computations in [b] are all scheduled after [c] *)
    body env b in
  List.map handler m_h_list
    
(** Causality analysis of a present handler *)
let present_handlers scondpat body env p_h_list h_opt =
  let handler { p_cond = scpat; p_body = b; p_env = p_env } =
    let env = build_env p_env env in
    let c = scondpat env scpat in
    (* computations in [b] are all scheduled after [c] *)
    body (Cenv.on env c) b in
  let tc_list = List.map handler p_h_list in
  match h_opt with
  | None -> tc_list
  | Some(h) -> (body env h) :: tc_list
               
(** causality of an expression. [C | H |- e: ct] *)
let rec exp env ({ e_desc = desc; e_typ = ty; e_loc = loc } as e) =
  let tc = match desc with
    | Econst _ | Econstr0 _ | Eperiod _ -> Causal.skeleton ty
    | Eglobal { lname = lname } ->
        let { info = info } = Modules.find_value lname in
        Causal.instance info ty
    | Elocal(x) ->
        let { t_typ = tc } = try read loc x env with Not_found -> print x in
        tc
    | Elast(x) ->
        let { t_last_typ = tc_opt } =
          try Cenv.last x env with Not_found -> print x in
        let tc = match tc_opt with | None -> assert false | Some(tc) -> tc in
        tc
    | Etuple(e_list) ->
        product (List.map (exp env) e_list)
    | Eop(op, e_list) ->
        operator env op ty e_list
    | Eapp(_, e, e_list) ->
        app env (exp env e) e_list
    | Erecord_access(e_record, _) ->
        let c = Causal.new_var () in
        exp_less_than_on_c env e_record c;
        Causal.skeleton_on_c c ty
    | Erecord(l) ->
        let c = Causal.new_var () in
        List.iter
          (fun (_, e) -> exp_less_than_on_c env e c) l;
        Causal.skeleton_on_c c ty
    | Etypeconstraint(e, _) -> exp env e
    | Elet(l, e_let) ->
        let new_env = local env l in
        let tc = exp new_env e_let in
        tc
    | Eblock(b, e_block) ->
        let env = block_eq_list env b in
        let tc = exp env e_block in
        tc
    | Eseq(e1, e2) ->
        let c = Causal.new_var () in
        exp_less_than_on_c env e1 c;
        exp (Cenv.on env c) e2
    | Epresent(h_e_list, e_opt) ->
        present_handler_exp_list env h_e_list e_opt
    | Ematch(_, e, h_e_list) ->
        let c_e = Causal.new_var () in
        exp_less_than_on_c env e c_e;
        match_handler_exp_list (Cenv.on env c_e) h_e_list in
  let cset = Causal.vars S.empty tc in
  (* annotate [e] with causality variables *)
  e.e_caus <- S.elements cset;
  tc
  
(** Typing an application *)
and app env tc_fct arg_list =
  (* typing the list of arguments *)
  let rec args tc_fct = function
    | [] -> tc_fct
    | arg :: arg_list ->
        let tc1, tc2 = Causal.filter_arrow tc_fct in
        exp_less_than env arg tc1;
        args tc2 arg_list in
  args tc_fct arg_list
    
(** Typing an operator *)
and operator env op ty e_list =
  let c = Causal.new_var () in
  match op, e_list with
  | Eunarypre, [e] ->
      exp_less_than_on_c env e (Causal.new_var ());
      Causal.skeleton_on_c c ty
  | Efby, [e1;e2] ->
      exp_less_than_on_c env e2 (Causal.new_var ());
      exp_less_than_on_c env e1 c;
      Causal.skeleton_on_c c ty
  | Eminusgreater, [e1;e2] ->
      exp_less_than_on_c env e1 c;
      exp_less_than_on_c env e2 c;
      Causal.skeleton_on_c c ty
  | Eifthenelse, [e1; e2; e3] ->
      exp_less_than_on_c env e1 c;
      exp_less_than_on_c env e2 c;
      exp_less_than_on_c env e3 c;
      Causal.skeleton_on_c c ty
  | Eup, [e] ->
      (* [up(e)] does not depend instantaneously of itself *)
      exp_less_than_on_c env e (Causal.new_var ());
      Causal.skeleton_on_c c ty
  | Einitial, [] ->
      Causal.skeleton_on_c c ty 
  | (Etest | Edisc | Ehorizon), [e] ->
      exp_less_than_on_c env e c;
      Causal.skeleton_on_c c ty
  | Eaccess, [e1; e2] ->
      exp_less_than_on_c env e1 c;
      exp_less_than_on_c env e2 c;
      Causal.skeleton_on_c c ty
  | Eupdate, [e1; i; e2] ->
      exp_less_than_on_c env e1 c;
      exp_less_than_on_c env i c;
      exp_less_than_on_c env e1 c;
      Causal.skeleton_on_c c ty
  | Eslice _, [e] ->
      exp_less_than_on_c env e c;
      Causal.skeleton_on_c c ty
  | Econcat, [e1; e2] ->
      exp_less_than_on_c env e1 c;
      exp_less_than_on_c env e2 c;
      Causal.skeleton_on_c c ty     
  | _ -> assert false
    

and exp_less_than_on_c env e expected_c =
  let actual_tc = exp env e in
  let expected_tc = Causal.skeleton_on_c expected_c e.e_typ in
  less_than e.e_loc env actual_tc expected_tc;
  (* annotate [e] with causality variables *)
  e.e_caus <- [expected_c]

and exp_less_than env e expected_tc =
  let actual_tc = exp env e in
  less_than e.e_loc env actual_tc expected_tc;
  (* annotate [e] with causality variables *)
  e.e_caus <- S.elements (Causal.vars S.empty expected_tc)

(** Checking equations *)
and equation_list env eq_list = List.iter (equation env) eq_list

(* Typing of an equation. [env |-e : env_e < before_c] *)
(* all computations must be performed before instant [before_c] *)
and equation env { eq_desc = desc; eq_write = defnames; eq_loc = loc } =
  match desc with
  | EQeq(p, e) ->
      let ty_p = pattern env p in
      exp_less_than env e ty_p
  | EQpluseq(n, e) ->
      let ty_n =
        try let { t_typ = ty } = read loc n env in ty
        with Not_found -> print n in
      exp_less_than env e ty_n
  | EQder(n, e, e0_opt, h_e_list) ->
      let { t_typ = expected_ty } =
        try write loc n env with | Not_found -> print n in 
      let _ = exp env e in
      begin match h_e_list, e0_opt with
        | [], None -> ()
        | _ ->
            (* [present_handler_exp_list] expects its arguments *)
            (* [h_e_list <> []] or [e0_opt <> None] *)            
            let actual_ty = present_handler_exp_list env h_e_list e0_opt in
            less_than loc env actual_ty expected_ty
      end
  | EQinit(n, e0) ->
      let { t_typ = ty_n } =
        try write loc n env with | Not_found -> print n in 
      exp_less_than env e0 ty_n
  | EQnext(n, e, e0_opt) ->
      (* [e] does not impose a causality constraint on [n] *)
      let _ = exp env e in
      let { t_typ = ty } = try write loc n env with Not_found -> print n in
      Misc.optional_unit (fun _ e0 -> exp_less_than env e0 ty) () e0_opt
  | EQautomaton(is_weak, s_h_list, se_opt) ->
      (* Typing a state expression *)
      let state env { desc = desc } =
        let c = Causal.new_var () in
        match desc with
        | Estate0 _ -> ()
        | Estate1(_, e_list) ->
            List.iter (fun e -> exp_less_than_on_c env e c) e_list in
      (* Typing of handlers *)
      (* scheduling is done this way: *)
      (* - Automata with strong preemption: *)
      (*   1. compute unless conditions; *)
      (*   2. execute the corresponding handler. *)
      (* - Automata with weak preemption: *)
      (*   1. compute the body; 2. compute the next active state. *)
      (* the causality constraints must reproduce this scheduling *)
      let handler env { s_body = b; s_trans = trans; s_env = s_env } =
        (* typing an escape. *)
        let escape env
            { e_cond = sc; e_block = b_opt; e_next_state = ns; e_env = e_env } =
          let env = build_env e_env env in
          let c_e = scondpat env sc in
          let env =
            Misc.optional
              (fun env b -> block_eq_list (Cenv.on env c_e) b) env b_opt in
          state env ns in
        let env = build_env s_env env in
        if is_weak then
          let env = block_eq_list env b in
          List.iter (escape (Cenv.push env)) trans
        else
          let env = Cenv.push env in
          let _ = List.iter (escape env) trans in
          ignore (block_eq_list env b) in
      List.iter (handler env) s_h_list;
      Misc.optional_unit state env se_opt
  | EQmatch(_, e, m_h_list) ->
      let c = Causal.new_var () in
      exp_less_than_on_c env e c;
      match_handler_block_eq_list (Cenv.on env c) m_h_list
  | EQpresent(p_h_list, b_opt) ->
      present_handler_block_eq_list env p_h_list b_opt
  | EQreset(eq_list, e) ->
      let c_e = Causal.new_var () in
      exp_less_than_on_c env e c_e;
      equation_list env eq_list
  | EQand(and_eq_list) ->
      equation_list env and_eq_list 
  | EQbefore(before_eq_list) ->
      equation_list env before_eq_list 
  | EQemit(n, e_opt) ->
      let c = Causal.new_var () in
      Misc.optional_unit (fun _ e -> exp_less_than_on_c env e c) () e_opt;
      let { t_typ = expected_ty } =
        try write loc n env with Not_found -> print n in
      let actual_ty = Causal.annotate (Cname n) (atom c) in
      less_than loc env actual_ty expected_ty
  | EQblock(b_eq_list) ->
      ignore (block_eq_list env b_eq_list)
  | EQforall { for_index = i_list; for_init = init_list; for_body = b_eq_list;
               for_out_env = o_env } ->
      (* Build the typing environment for inputs/outputs *)
      (* and build an association table [oi out o] for all output pairs *)
      let index (io_env, oi2o) { desc = desc } =
        match desc with
        | Einput(x, e) ->
            let in_c = Causal.new_var () in
            exp_less_than_on_c env e in_c;
            let ty_arg, _ = Types.filter_vec e.e_typ in
            let tc = Causal.skeleton_on_c in_c ty_arg in
            Env.add x { t_typ = tc; t_last_typ = Some(fresh tc) } io_env,
            oi2o
        | Eindex(x, e1, e2) ->
            let in_c = Causal.new_var () in
            exp_less_than_on_c env e1 in_c;
            exp_less_than_on_c env e2 in_c;
            let tc = Causal.skeleton_on_c in_c e1.e_typ in
            Env.add x { t_typ = tc; t_last_typ = Some(fresh tc) } io_env,
            oi2o
      | Eoutput(oi, o) ->
        let out_c = Causal.new_var () in
        let { Deftypes.t_typ = ty } = Env.find oi o_env in
        let tc = Causal.skeleton_on_c out_c ty in
        Env.add oi { t_typ = tc; t_last_typ = Some(fresh tc) } io_env,
        Env.add oi o oi2o in
        
       (* typing the initialization *)
       let init init_env { desc = desc } =
         match desc with
         | Einit_last(x, e) ->
            let tc = exp env e in
            Env.add x { t_typ = fresh tc; t_last_typ = Some(tc) } init_env in

       (* build the typing environment for read variables from the header *)
       let io_env, oi2o = List.fold_left index (Env.empty, Env.empty) i_list in

       (* build the typing environment for accummulation variables *)
       let init_env = List.fold_left init Env.empty init_list in

       (* build the typing environment *)
       let env = Cenv.append io_env env in
       let env = Cenv.append init_env env in
              
       (* type the body *)
       ignore (block_eq_list env b_eq_list)

(* Typing a present handler for expressions *)
(* The handler list is not be empty *)
and present_handler_exp_list env p_h_list e_opt =
  (* [spat -> e]: the result both depend on [spat] and [e] *)
  let tc_list =
    present_handlers scondpat exp env p_h_list e_opt in
  Causal.suptype_list true tc_list

(* Typing a present handler for blocks *)
and present_handler_block_eq_list env p_h_list p_h_opt =
  (* [spat -> body]: all outputs from [body] depend on [spat] *)
  ignore (present_handlers scondpat block_eq_list env p_h_list p_h_opt)

(* Typing a match handler for expressions *)
(* The handler list is not empty *)
and match_handler_exp_list env m_h_list =
  let tc_list = match_handlers exp env m_h_list in
  Causal.suptype_list true tc_list

(* Typing a match handler for blocks. *)
and match_handler_block_eq_list env m_h_list =
  ignore (match_handlers block_eq_list env m_h_list)

(* Typing a block with a set of equations in its body. *)
(* if [defnames = {x1,..., xn} with x1:ct1;...;xn:ctn *)
(* add [x1:ct'1;...;xn:ct'n] st ct'1 < ct1,..., ct'n < ctn *)
(* and type check in the extended environment *)
and block_eq_list env
    { b_locals = l_list; b_body = eq_list;
      b_env = b_env; b_loc = loc; b_write = defnames } =
  let writes defnames env =
    let add x acc = Env.add x (write loc x env) acc in
    let env_defnames =
      Ident.S.fold add (Deftypes.names Ident.S.empty defnames) Env.empty in
    Cenv.append env_defnames env in 
  (* the block is executed atomically *)
  (* local equations are executed sequentially before the body *)
  (* typing local definitions *)
  let env = List.fold_left (fun env l -> local env l) env l_list in
  (* Build the typing environment for names introduced by a *)
  (* [local x1,..., xn in ...] *)
  let env = build_env b_env env in
  equation_list (writes defnames env) eq_list;
  env

(* Typing a local declaration. Returns the extended environment *)
and local env { l_eq = eq_list; l_env = l_env; l_loc = loc } =
  (* First extend the typing environment *)
  let env = build_env l_env env in
  (* Then type the body *)
  List.iter (equation env) eq_list;
  env

(* Typing  a signal pattern. *)
and scondpat env sc =
  let rec scondpat { desc = desc; loc = loc } expected_c =
    match desc with
    | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
      scondpat sc1 expected_c; scondpat sc2 expected_c
    | Econdon(sc1, e) ->
       exp_less_than_on_c env e expected_c;
       scondpat sc1 expected_c
    | Econdexp(e) ->
       exp_less_than_on_c env e expected_c
    | Econdpat(e, p) ->
       exp_less_than_on_c env e expected_c;
       let actual_ty = pattern env p in
       let expected_ty = Causal.skeleton_on_c expected_c p.p_typ in
       less_than p.p_loc env actual_ty expected_ty in
  let expected_c = Causal.new_var () in
  scondpat sc expected_c;
  expected_c

let implementation ff { desc = desc } =
  try
    match desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(f, _, e) ->
       Misc.push_binding_level ();
       let tc = exp Cenv.empty e in
       Misc.pop_binding_level ();
       let tcs = generalise tc in
       Global.set_causality (Modules.find_value (Lident.Name(f))) tcs;
       (* output the signature *)
       if !Misc.print_causality_types then Pcaus.declaration ff f tcs
    | Efundecl (f, { f_kind = k; f_atomic = atomic;
                     f_args = p_list; f_body = e; f_env = h0 }) ->
       Misc.push_binding_level ();
       let env = build_env h0 Cenv.empty in
       let actual_ty_res = exp env e in
       let expected_ty_list, expected_ty_res =
         (* for an atomic node, all outputs depend on all inputs *)
         if atomic then
           (* first type the body *)
           let c = Causal.new_var () in
           let tc_arg_list =
             List.map
               (fun p -> subtype false (Causal.skeleton_on_c c p.p_typ))
               p_list in
           let tc_res = subtype true (Causal.skeleton_on_c c e.e_typ) in
           tc_arg_list, tc_res
         else
           List.map (fun p -> Causal.skeleton p.p_typ) p_list,
           Causal.skeleton e.e_typ in
       less_than e.e_loc env actual_ty_res expected_ty_res;
       List.iter2
         (fun p expected_ty -> let actual_ty = pattern env p in
           less_than p.p_loc env expected_ty actual_ty) p_list expected_ty_list;
       Misc.pop_binding_level ();
       let tcs =
         generalise (Causal.funtype_list expected_ty_list expected_ty_res) in
       (* then add the current entries in the global environment *)
       Global.set_causality (Modules.find_value (Lident.Name(f))) tcs;
       (* output the signature *)
       if !Misc.print_causality_types then Pcaus.declaration ff f tcs
  with
  | Error(loc, kind) -> message loc kind

let implementation_list ff impl_list =
  List.iter (implementation ff) impl_list;
  impl_list
