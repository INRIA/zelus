(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2018                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* initialization check *)

(* we do very simple check, following STTT'04.
 *- E.g., [init x = e] and [pre(e)] are
 *- valid if [e] is initialized.
 *- when x is declared with [init x = e], then last x is
 *- marked to be initialized with type 0 if [x = ...] at discrete instants;
 *- 1/2 otherwise. if x is not explicitly initialized, it gets type 1 *)
open Misc
open Ident
open Global
open Zelus
open Location
open Deftypes
open Definit
open Init

(* Main error message *)
type error =
  | Iless_than of ty * ty (* not (expected_ty < actual_ty) *) 
  | Iless_than_i of t * t (* not (expected_i < actual_i) *) 
  | Ilast of Ident.t (* [last x] is un-initialized *)

exception Error of location * error

let error loc kind = raise (Error(loc, kind))

let message loc kind =
  begin
    match kind with
    | Iless_than(expected_ty, actual_ty) ->
        Format.eprintf
          "%aInitialization error: this expression \
           has type %a which should be less than %a.@."
          output_location loc
          Pinit.ptype expected_ty Pinit.ptype actual_ty
    | Iless_than_i(expected_i, actual_i) ->
        Format.eprintf
          "%aInitialization error: this expression \
           has type %a which should be less than %a.@."
          output_location loc
          Pinit.init expected_i Pinit.init actual_i
    | Ilast(n) ->
        Format.eprintf
          "%aInitialization error: the last value of %s \
           may not be well initialized.@."
          output_location loc
          (Ident.source n)
  end;
  raise Misc.Error

let less_than loc actual_ty expected_ty =
  try
    Init.less actual_ty expected_ty
  with
    | Init.Clash _ -> error loc (Iless_than(actual_ty, expected_ty))

let less_for_last loc n actual_i expected_i =
  try
    Init.less_i actual_i expected_i
  with
    | Init.Clash _ -> error loc (Ilast(n))

(** An entry in the type environment *)
type tentry =
    { t_typ: Definit.ty; (* the init type [ty] of x *)
      t_last: Definit.t; (* v in [0, 1/2, 1] so that last x: ty[v] *)
    }
    
(** Build an environment from a typing environment *)
(* if [x] is defined by [init x = e] then
 *- [x] is initialized; [last x: 0] if [x] declared in a discrete
 *- context; [last x: a] otherwise.
 *- when [x = e] then [1/2 < a] if the equation is activated in discrete time *)
let build_env is_continuous l_env env =
  let entry { Deftypes.t_sort = sort; Deftypes.t_typ = ty } =
    match sort with 
    | Deftypes.Smem { Deftypes.m_init = Some _ } | Deftypes.Svar _ ->
        (* [x] and [last x] or or [x] and [next x] *)
        (* are well initialized *)
        let lv, iv =
          if is_continuous then Init.new_var (), izero else izero, izero in
        { t_last = lv; t_typ = Init.skeleton_on_i iv ty }
    | Deftypes.Smem { Deftypes.m_previous = true } ->
        (* [x] initialized; [last x] uninitialized *)
        { t_last = ione; t_typ = Init.skeleton_on_i izero ty }
    | Deftypes.Sstatic | Deftypes.Sval | Deftypes.Smem _ -> 
        (* no constraint *)
        let lv = if is_continuous then ihalf else izero in
        { t_last = lv; t_typ = Init.skeleton ty } in
  Env.fold (fun n tentry acc -> Env.add n (entry tentry) acc) l_env env

(* Given an environment [env], returns a new one the bottom type becomes *)
(* 1/2 instead of 0 *)
let half env = env
  
(* copy an environment where any name from [dv] does not have any *)
(* constraint on its last value. This is useful in two cases:
 *- when typing all the branches of a control structures; a variable [x]
 *- defined in one branch but not in an other one is such that [x = last x]
 *- in this branch, and thus, [last x: t] with no constraint on t.
 *- when typing an automaton. Every variable defined in the initial state 
 *- has a well initialized last value in the remaining states, provided all
 *- transitions in the initial state are weak. *)
let add_last_to_env env { dv = dv } =
  let add n env =
    let { t_typ = typ } = Env.find n env in
    Env.add n { t_typ = typ; t_last = Init.new_var () } env in
  Ident.S.fold add dv env

    
(* find the initial handler from an automaton. Returns it with its complement *)
let split se_opt s_h_list =
  let statepat { desc = desc } =
    match desc with
      | Estate0pat(id) | Estate1pat(id, _) -> id in
  let state { desc = desc } =
    match desc with
      | Estate0(id) | Estate1(id, _) -> id in
  let rec splitrec s s_h_list =
    match s_h_list with
      | [] -> assert false
      | { s_state = spat } as s_h :: s_h_list -> 
          if s = statepat spat then s_h, s_h_list
          else 
            let s_h0, s_h_list = splitrec s s_h_list in
            s_h0, s_h :: s_h_list in
  match se_opt with
    | None -> (* the starting state is the first in the list *)
        List.hd s_h_list, List.tl s_h_list
    | Some(se) -> splitrec (state se) s_h_list

let print x = Misc.internal_error "unbound" Printer.name x


(** Check that partially defined names have a last value which is initialized *)
let initialized_last loc env defnames_list =
  (* computes the set of names which are partially defined *)
  let
      (_, dv_partial), (_, di_partial), _, (_, nv_partial), (_, mv_partial) =
    Total.merge_defnames_list defnames_list in
  (* check that all of them have a well-initialized initial value *)
  let check n =
    let { t_last = last } = try Env.find n env with Not_found -> assert false in
    less_for_last loc n last izero in
  Ident.S.iter check dv_partial;
  Ident.S.iter check di_partial;
  Ident.S.iter check nv_partial;
  Ident.S.iter check mv_partial
  

(** Patterns *)
(* [pattern env p expected_ty] means that the type of [p] must be less *)
(* than [expected_ty] *)
let rec pattern is_continuous env
    { p_desc = desc; p_loc = loc; p_typ = ty } expected_ty =
  match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> ()
    | Evarpat(x) -> 
        let ty1, last =
          try let { t_typ = ty1; t_last = last } = Env.find x env in ty1, last 
          with | Not_found -> assert false in
        less_than loc expected_ty ty1;
        (* an equation [x = e] in a continuous context is correct *)
        (* if x and e have the same type and [last x: t] with [1/2 <= t] *)
        if is_continuous then less_for_last loc x ihalf last
    | Etuplepat(pat_list) ->
        let ty_list = Init.filter_product expected_ty in
        List.iter2 (pattern is_continuous env) pat_list ty_list
    | Erecordpat(l) -> 
        let pattern_less_than_on_i pat i =
          let expected_ty = Init.skeleton_on_i i pat.p_typ in
          pattern is_continuous env pat expected_ty in
        let i = Init.new_var () in
        less_than loc expected_ty (Init.skeleton_on_i i ty);
        List.iter (fun (_, p) -> pattern_less_than_on_i p i) l
    | Etypeconstraintpat(p, _) -> pattern is_continuous env p expected_ty
    | Eorpat(p1, p2) -> 
        pattern is_continuous env p1 expected_ty;
        pattern is_continuous env p2 expected_ty
    | Ealiaspat(p, n) -> 
        pattern is_continuous env p expected_ty;
        let ty_n, last = 
          try let { t_typ = ty1; t_last = last } = Env.find n env in ty1, last
          with | Not_found -> assert false in
        less_than loc expected_ty ty_n;
        if is_continuous then less_for_last loc n izero last

(** Blocks *)
let block is_continuous
    locals body env { b_locals = l_list; b_body = bo; b_env = b_env } =
  (* First extend the typing environment *)
  let env = build_env is_continuous b_env env in
  let env = locals is_continuous env l_list in
  body is_continuous env bo;
  env

(** Match handler *)
let match_handlers is_continuous body env m_h_list =
  let handler { m_env = m_env; m_body = b } =
    let env = build_env is_continuous m_env env in
    body is_continuous env b in
  List.iter handler m_h_list

(** Present handler *)
let present_handlers is_continuous scondpat body env p_h_list =
  let handler { p_cond = scpat; p_body = b; p_env = p_env } =
    let env = build_env is_continuous p_env env in
    scondpat is_continuous env scpat;
    let env = if is_continuous then half env else env in
    body false env b in
  List.iter handler p_h_list

(** Initialization of an expression *)
let rec exp is_continuous env { e_desc = desc; e_typ = ty } =
  match desc with
  | Econst _
  | Econstr0 _
  | Eperiod _ -> Init.skeleton_on_i (Init.new_var ()) ty
  | Eglobal { lname = lname } ->
    let { info = info } =
      try Modules.find_value lname with | Not_found -> assert false in
    Init.instance info ty
  | Elocal(x) -> 
     begin try let { t_typ = ty1 } = Env.find x env in ty1 
           with | Not_found -> print x
     end
  | Elast(x) -> 
     begin try 
         (* [last x] is initialized only if an equation [init x = e] *)
         (* appears and [e] is also initialized *)
         let { t_typ = typ; t_last = last } = Env.find x env in
         Init.fresh_on_i last typ
       with 
       | Not_found -> Init.skeleton_on_i ione ty end
  | Etuple(e_list) -> 
     product (List.map (exp is_continuous env) e_list)
  | Eop(op, e_list) -> operator is_continuous env op ty e_list
  | Eapp(_, e, e_list) ->
     app is_continuous env (exp is_continuous env e) e_list
  | Erecord_access(e_record, _) -> 
     let i = Init.new_var () in
     exp_less_than_on_i is_continuous env e_record i;
     Init.skeleton_on_i i ty
  | Erecord(l) -> 
     let i = Init.new_var () in
     List.iter (fun (_, e) -> exp_less_than_on_i is_continuous env e i) l;
     Init.skeleton_on_i i ty
  | Etypeconstraint(e, _) -> exp is_continuous env e
  | Elet(l, e_let) -> 
     let env = local is_continuous env l in
     exp is_continuous env e_let
  | Eblock(b, e_block) ->
     let env = block_eq_list is_continuous env b in
     exp is_continuous env e_block
  | Eseq(e1, e2) -> 
     ignore (exp is_continuous env e1);
     exp is_continuous env e2
  | Epresent(p_h_list, e_opt) ->
    (* if [e] returns a tuple, all type element are synchronised, i.e., *)
    (* if one is un-initialized, the whole is un-initialized *)
    let ty = Init.skeleton_on_i (Init.new_var ()) ty in
    let _ =
      Misc.optional_map (fun e -> exp_less_than is_continuous env e ty) e_opt in
    present_handler_exp_list is_continuous env p_h_list ty;
    ty
  | Ematch(_, e, m_h_list) ->
    (* we force [e] to be always initialized. This is overly constraining *)
    (* but correct and simpler to justify *)
    exp_less_than_on_i is_continuous env e izero;
    let ty = Init.skeleton_on_i (Init.new_var ()) ty in
    match_handler_exp_list is_continuous env m_h_list ty;
    ty
       
(** Typing an operator *)
and operator is_continuous env op ty e_list =
  match op, e_list with
  | Eunarypre, [e] -> 
      (* input of a unit delay must be of type 0 *)
      exp_less_than_on_i is_continuous env e izero; 
     Init.skeleton_on_i ione ty
  | Efby, [e1;e2] ->
      (* right input of a initialized delay must be of type 0 *)
      exp_less_than_on_i is_continuous env e2 izero;
     exp is_continuous env e1
  | Eminusgreater, [e1;e2] ->
     let t1 = exp is_continuous env e1 in
     let _ = exp is_continuous env e2 in
     t1
  | Eifthenelse, [e1; e2; e3] ->
     (* a conditional does not force all element to be initialized *)
     let i = Init.new_var () in
     exp_less_than_on_i is_continuous env e1 i;
     exp_less_than_on_i is_continuous env e2 i;
     exp_less_than_on_i is_continuous env e3 i;
     Init.skeleton_on_i i ty
  | (Einitial | Eup | Etest | Edisc
    | Eaccess | Eupdate | Eslice _ | Econcat), e_list ->
      (* here, we force the argument to be always initialized *)
      (* this is necessary for [up(x)] and access functions to arrays; not *)
      (* for the others *)
      let iv = izero in
      List.iter (fun e -> exp_less_than_on_i is_continuous env e iv) e_list;
     Init.skeleton_on_i iv ty
  | _ -> assert false


(** Typing an application *)
and app is_continuous env ty_fct arg_list =
  (* typing the list of arguments *)
  let rec args ty_fct = function
    | [] -> ty_fct
    | arg :: arg_list ->
       let ty1, ty2 = Init.filter_arrow ty_fct in
       exp_less_than is_continuous env arg ty1;
       args ty2 arg_list in
  args ty_fct arg_list

and exp_less_than_on_i is_continuous env e expected_i =
  let actual_ty = exp is_continuous env e in
  less_than e.e_loc actual_ty (Init.skeleton_on_i expected_i e.e_typ)

and opt_exp_less_than_on_i is_continuous env e_opt expected_i =
  match e_opt with
  | None -> ()
  | Some(e) -> exp_less_than_on_i is_continuous env e expected_i

and exp_less_than is_continuous env e expected_ty =
  let actual_ty = exp is_continuous env e in
  less_than e.e_loc actual_ty expected_ty

(** Checking equations *)
and equation_list is_continuous env eq_list =
  List.iter (equation is_continuous env) eq_list

and equation is_continuous env
    { eq_desc = eq_desc; eq_loc = loc; eq_write = defnames } =
  match eq_desc with
  | EQeq(p, e) -> 
      let ty = exp is_continuous env e in
      pattern is_continuous env p ty
  | EQpluseq(n, e) ->
      let ty_n =
        try let { t_typ = ty } = Env.find n env in ty
        with Not_found -> assert false in
      exp_less_than is_continuous env e ty_n
  | EQder(n, e, e0_opt, p_h_e_list) ->
      (* e must be of type 0 *)
      let ty_n, last = 
        try let { t_typ = ty1; t_last = last1 } = Env.find n env in 
          ty1, last1 
        with | Not_found -> assert false in
      exp_less_than is_continuous env e ty_n;
      less_than loc ty_n (Init.skeleton_on_i Init.izero e.e_typ);
      (match e0_opt with
       | Some(e0) -> exp_less_than_on_i false env e0 ihalf
       | None -> less_for_last loc n last izero);
      present_handler_exp_list is_continuous env p_h_e_list ty_n
  | EQinit(n, e0) ->
      exp_less_than_on_i false env e0 ihalf
  | EQnext(n, e, e0_opt) ->
      let ty_n, last =
        try let { t_typ = ty1; t_last = last1 } = Env.find n env in
          ty1, last1
        with Not_found -> assert false in
      exp_less_than is_continuous env e ty_n;
      (match e0_opt with
       | Some(e0) -> exp_less_than_on_i false env e0 ihalf
       | None -> less_for_last loc n last izero);
      less_than e.e_loc (Init.skeleton_on_i izero e.e_typ) ty_n
  | EQautomaton(is_weak, s_h_list, se_opt) ->
      (* state *)
      let state env { desc = desc } =
        match desc with
        | Estate0 _ -> ()
        | Estate1(_, e_list) -> 
            List.iter
              (fun e -> exp_less_than_on_i false env e izero) e_list in
      (* handler *)
      let handler env { s_body = b; s_trans = trans; s_env = s_env } =
        let escape env
            { e_cond = sc; e_block = b_opt; e_next_state = ns;
              e_env = e_env } =
          let env = build_env is_continuous e_env env in
          scondpat is_continuous env sc;
          let env = 
            match b_opt with
            | None -> env | Some(b) -> block_eq_list false env b in
          state env ns in
        let env = add_last_to_env env defnames in
        let env = build_env is_continuous s_env env in
        let env = block_eq_list is_continuous env b in
        List.iter (escape env) trans in
      (* do a special treatment for the initial state *)
      let first_s_h, remaining_s_h_list = split se_opt s_h_list in
      (* first type the initial branch *)
      handler env first_s_h;
      (* if the initial state has only weak transition then all *)
      (* variables from [defined_names] do have a last value *)
      let defnames_initial_state = first_s_h.s_body.b_write in
      let env =
        if is_weak then add_last_to_env env defnames_initial_state else env in
      List.iter (handler env) remaining_s_h_list;
      (* every partially defined value must have an initialized value *)
      let defnames_list =
        List.map (fun { s_body = { b_write = w } } -> w) remaining_s_h_list in
      initialized_last loc env (defnames_initial_state :: defnames_list);
      (* finaly check the initialisation *)
      ignore (Misc.optional_map (state env) se_opt)
  | EQmatch(total, e, m_h_list) ->
      exp_less_than_on_i is_continuous env e izero;
      match_handler_block_eq_list is_continuous env defnames m_h_list;
      (* every partially defined value must have an initialized value *)
      let defnames_list =
        List.map (fun { m_body = { b_write = w } } -> w) m_h_list in
      let defnames_list = 
        if !total then defnames_list else Deftypes.empty :: defnames_list in
      initialized_last loc env defnames_list
  | EQpresent(p_h_list, b_opt) ->
      let _ =
        Misc.optional_map
          (fun b ->
             let env = add_last_to_env env defnames in
             ignore (block_eq_list is_continuous env b)) b_opt in
      present_handler_block_eq_list is_continuous env defnames p_h_list;
      (* every partially defined value must have an initialized value *)
      let defnames =
        match b_opt with
        | None -> Deftypes.empty | Some { b_write = w } -> w in
      let defnames_list =
        List.map (fun { p_body = { b_write = w } } -> w) p_h_list in
      initialized_last loc env (defnames :: defnames_list)       
  | EQreset(eq_list, e) -> 
      exp_less_than_on_i is_continuous env e izero;
      equation_list is_continuous env eq_list
  | EQand(eq_list)
  | EQbefore(eq_list) -> equation_list is_continuous env eq_list
  | EQemit(n, e_opt) ->
      let ty_n = 
        try let { t_typ = ty1 } = Env.find n env in ty1
        with | Not_found -> assert false in
      less_than loc ty_n (Init.atom izero);
      ignore
        (Misc.optional_map
           (fun e -> exp_less_than_on_i is_continuous env e izero) e_opt)
  | EQblock(b_eq_list) ->
      ignore (block_eq_list is_continuous env b_eq_list)
  | EQforall { for_index = i_list; for_init = init_list; for_body = b_eq_list;
               for_in_env = i_env; for_out_env = o_env } ->
      (* typing the declaration of indexes *)
      (* all bounds must be initialized *)
      let index env { desc = desc; loc = loc } =
        match desc with
        | Einput(_, e) -> exp_less_than_on_i is_continuous env e izero
        | Eindex(_, e1, e2) ->
            exp_less_than_on_i is_continuous env e1 izero;
            exp_less_than_on_i is_continuous env e2 izero
        | Eoutput(x, xout) ->
            let ti =
              try
                let { t_typ = ti } = Env.find xout env in ti
              with | Not_found -> assert false in
            less_than loc ti (Init.atom izero) in
      (* typing the initialization *)
      (* all right hand-side expressions must be initialized *)
      let init init_env { desc = desc } =
        match desc with
        | Einit_last(x, e) ->
            let ti = exp is_continuous env e in
            let tzero = Init.skeleton_on_i izero e.e_typ in
            less_than e.e_loc ti tzero;
            Env.add x { t_last = izero; t_typ = tzero } init_env in
      List.iter (index env) i_list;
      let init_env = List.fold_left init Env.empty init_list in
      let env = build_env is_continuous i_env env in
      let env = build_env is_continuous o_env env in
      let env = Env.append init_env env in
      ignore (block_eq_list is_continuous env b_eq_list)
        
(* typing rule for a present statement where the body is an expression
 *- if [is_continuous = true] this means that every handler [ze -> body]
 *- is necessarily activated on a zero-crossing instant, thus discretely.
 *- in that case, it is enough that the body has type 1/2 and the whole
 *- present expression will get type 0 *)
and present_handler_exp_list is_continuous env p_h_list ty =
  present_handlers is_continuous scondpat 
    (fun is_continuous env e -> exp_less_than is_continuous env e ty)
    env p_h_list

(* typing of a block of equations *)
and present_handler_block_eq_list is_continuous env defnames p_h_list =
  present_handlers is_continuous scondpat 
    (fun _ env b ->
       let env = add_last_to_env env defnames in
       ignore (block_eq_list is_continuous env b))
    env p_h_list

and match_handler_block_eq_list is_continuous env defnames m_h_list =
  match_handlers is_continuous 
    (fun is_continuous env b ->
       let env = add_last_to_env env defnames in
       ignore (block_eq_list is_continuous env b))
    env m_h_list

and match_handler_exp_list is_continuous env m_h_list ty =
  match_handlers is_continuous 
    (fun is_continuous env e -> exp_less_than is_continuous env e ty)
    env m_h_list

and block_eq_list is_continuous env b =
  let locals is_continuous env l_list =
    List.fold_left (local is_continuous) env l_list in
  block is_continuous locals equation_list env b

and local is_continuous env { l_eq = eq_list; l_loc = loc; l_env = l_env } =
  (* First extend the typing environment *)
  let env = build_env is_continuous l_env env in
  (* then type the body *)
  List.iter (equation is_continuous env) eq_list; env
  
(* we force that the signal pattern be initialized. E.g.,
*- [present s(x) -> ...] gives the type 0 to s and x *)
and scondpat is_continuous env { desc = desc } =
  match desc with
  | Econdand(sc1, sc2) | Econdor(sc1, sc2) -> 
      scondpat is_continuous env sc1; scondpat is_continuous env sc2
  | Econdon(sc1, e) ->
      scondpat is_continuous env sc1;
      exp_less_than_on_i is_continuous env e izero
  | Econdexp(e) | Econdpat(e, _) -> 
      exp_less_than_on_i is_continuous env e izero
        
let implementation ff impl =
  try
    match impl.desc with
    | Eopen _ | Etypedecl _ -> ()
    | Econstdecl(f, _, e) ->
        (* the expression [e] must be initialized *)
        let ty_zero = Init.skeleton_on_i izero e.e_typ in
        Misc.push_binding_level ();
        exp_less_than false Env.empty e ty_zero;
        Misc.pop_binding_level ();
        let tys = generalise ty_zero in
        Global.set_init (Modules.find_value (Lident.Name(f))) tys;
        (* output the signature *)
        if !Misc.print_initialization_types then Pinit.declaration ff f tys
    | Efundecl(f, { f_kind = k; f_atomic = atomic; f_args = p_list;
                    f_body = e; f_env = h0 }) -> 
        let is_continuous = match k with | C -> true | _ -> false in
        Misc.push_binding_level ();
        let env = build_env is_continuous h0 Env.empty in
        let ty_list = List.map (fun p -> Init.skeleton p.p_typ) p_list in
        List.iter2 (pattern is_continuous env) p_list ty_list;
        let ty_res = exp is_continuous env e in
        let actual_ty = funtype_list ty_list ty_res in
        (* for an atomic node, all outputs depend on all inputs *)
        let expected_ty =
          if atomic then
          (* first type the body *)
            let i = Init.new_var () in
            let ty_arg_list =
              List.map (fun p -> Init.skeleton_on_i i p.p_typ) p_list in
            let ty_res = Init.skeleton_on_i i e.e_typ in
            funtype_list ty_arg_list ty_res
          else
            funtype_list (List.map (fun p -> Init.skeleton p.p_typ) p_list)
              (Init.skeleton e.e_typ) in
        Init.less actual_ty expected_ty;
        Misc.pop_binding_level ();
        let tys = generalise actual_ty in
        Global.set_init (Modules.find_value (Lident.Name(f))) tys;
        (* output the signature *)
        if !Misc.print_initialization_types then Pinit.declaration ff f tys
  with
  | Error(loc, kind) -> message loc kind
                          
let implementation_list ff impl_list =
  List.iter (implementation ff) impl_list; impl_list
