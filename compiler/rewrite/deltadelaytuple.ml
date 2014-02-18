open Hybrid
open Misc
open Global
open Deftypes

(* TODO: add some comments to describe the principle of the translation *)

(* TODO: preserve structure of lets (i.e. order) during hybrid expansion *)

(** deltadelay translation; LCTES 2011 submission **)

let typ_bool = Initial.typ_bool
let typ_float = Initial.typ_float

let empty_id_set = Ident.S.empty

(* Helper functions for code generation *)

(* TODO: extend to handle external nodes *)
let flatten_typ_arg arrname typ =
  let arrele n = Obc.Oarrele (arrname, Obc.make (Obc.Oconst (Obc.Oint n))) in
  let neq_zero e =
    Obc.Oapp (Lident.Name "<>", [e; Obc.make (Obc.Oconst (Obc.Oint32 0))])
  in
  let rec f n ty =
    match ty.t_desc with
    | Tconstr (l, _, _) when l = Initial.unit_ident ->
        (n, Obc.Oconst Obc.Ovoid)
    | Tconstr (l, _, _) when l = Initial.float_ident ->
        (n + 1, arrele n)
    | Tconstr (l, _, _) when l = Initial.bool_ident ->
        (n + 1, neq_zero (Obc.make (arrele n)))
    | Tproduct tys ->
        let (n, tys) = List.fold_left fl (n, []) tys in
        (n, Obc.Otuple (List.rev tys))
    | Tlink ty ->
        f n ty
    | _ -> assert false
  and fl (n, rs) ty = let (n, r) = f n ty in (n, Obc.make r::rs)
  in
  Obc.make (snd (f 0 typ))

(* TODO: extend to handle external nodes *)
let typ_to_ctally typ =
  let rec f n ty =
    match ty.t_desc with
    | Tconstr (l, _, _) when l = Initial.unit_ident  -> n
    | Tconstr (l, _, _) when l = Initial.float_ident -> n + 1
    | Tconstr (l, _, _) when l = Initial.bool_ident -> n + 1
    | Tproduct tys -> List.fold_left f n tys
    | Tlink ty     -> f n ty
    | _ -> assert false
  in
  f 0 typ

(* TODO: extend to handle external nodes *)
let flatten_typ_pat prefix typ =
  let rev_vars (n, vars, r) = (List.rev vars, Obc.make r) in
  let rec f n vars ty =
    match ty.t_desc with
    | Tconstr (l, _, _) when l = Initial.float_ident ->
        let v = Ident.fresh prefix in
        (n + 1, v::vars, Obc.Ovarpat v)

    | Tconstr (l, _, _) when l = Initial.bool_ident ->
        let v = Ident.fresh prefix in
        (n + 1, v::vars, Obc.Ovarpat v)

    | Tproduct tys ->
        let (n, vars, tys) = List.fold_left fl (n, vars, []) tys in
        (n, vars, Obc.Otuplepat (List.rev tys))

    | Tlink ty -> f n vars ty
    | _ -> (n, vars, Obc.Owildpat)

  and fl (n, vars, rs) ty =
    let (n, vars, r) = f n vars ty in
    (n, vars, Obc.make r::rs)
  in
  rev_vars (f 0 [] typ)

let assign_from_vars arrname vars after =
  let f (n, r) v =
    let idx = Obc.make (Obc.Oconst (Obc.Oint n)) in
    let var = Obc.make (Obc.Olocal (v, Obc.Val)) in
    let assign = Obc.Oarrassign (arrname, idx, var) in
    (n + 1, Obc.make (Obc.Osequence (Obc.make assign, r)))
  in
  snd (List.fold_left f (0, after) vars)

(* Utility functions and contexts *)

let make desc = { desc = desc; loc = Location.no_location }
let local n = make (Elocal(n))

let fval_zero = make (Econst (Efloat 0.0))
let fval_one = make (Econst (Efloat 1.0))
let val_unit = make (Econst Evoid)
let val_false = make (Econst (Ebool false))

type ctx =
    {
      (* zero-crossing pair:
           zero: input from the solver indicating which
                 zero-crossings have been detected
           upv : output to the solver indicating the current
                 value of an expression to watch for zero-crossings

         The type of a simple pair is:
            zero : bool
            upv  : float
         but the values passed to and from function applications
         are, in general, trees of bools, floats, and units. The
         unit type indicates that a hybrid function does not contain
         any zero-crossings.
       *)
      zero    : (Ident.t * typ) State.t;
      upv     : (Ident.t * typ) State.t;

      (* continuous-state triple:
           lastx: input from the solver giving the (approximated)
                  value of a continuous variable
           diffx: output to the solver giving the instantaneous
                  derivative of a continuous variable
           nextx: a local variable holding the current value of a
                  continuous variable, which will be equal to the
                  corresponding lastx when there is no reset.
                  these names are tracked because they may need to
                  be made local at the block level (for instance,
                  when not shared across the states of an
                  automaton)
           TODO: rename to 'currx' or 'thisx'

         The types of simple instances are:
            lastx : float
            diffx : float
            nextx : float
         but the values passed to and from function applications
         are, in general, trees of floats and units. The unit type
         indicates that a hybrid function does not contain any
         continuous states.
       *)
      lastx   : (Ident.t * typ) State.t;
      nextx   : (Ident.t * typ) State.t;
      diffx   : (Ident.t * typ) State.t;

      (* eqs: the set of equations built during rewriting.
         eqs_evn: map variable names in eqs to types, this
                  is needed to build a let/in.
       *)
      eqs     : eq State.t;
      eqs_env : Deftypes.tentry Ident.Env.t;

      (* This is the set of local variables that need to be hidden
         again when we mint a block. For instance, when rewriting
         within a state of an automaton we flatten everything, but
         then we need to hide certain variables at the state level
         to avoid implicit sharing across states.*)
      locals  : Ident.S.t;

      inits   : eq State.t;

      (* This map is used to replace expressions of the type `last x',
         where x is a continuous variable approximated by the solver,
         with the corresponding input 'lx' from the solver.*)
      lastmap : Ident.t Ident.Env.t;
    }

let env_add env0 (id, ty) =
  Ident.Env.add id { t_sort = Val; t_typ = ty } env0

let env_adds env0 xs =
  List.fold_left env_add env0 xs
      
let empty = 
  { zero    = State.empty;
    upv     = State.empty;
    lastx   = State.empty;
    nextx   = State.empty;
    diffx   = State.empty;
    eqs     = State.empty;
    eqs_env = Ident.Env.empty;
    locals  = Ident.S.empty;
    inits   = State.empty;
    lastmap = Ident.Env.empty; }

let pair  
    { zero = zv1; upv = up1; lastx = lv1; nextx = xv1; diffx = dx1; eqs = eq1;
      eqs_env = eqs_env1; locals = locals1; inits = inits1; lastmap = lastmap1 }
    { zero = zv2; upv = up2; lastx = lv2; nextx = xv2; diffx = dx2; eqs = eq2;
      eqs_env = eqs_env2; locals = locals2; inits = inits2; lastmap = lastmap2 }
    =
    { zero    = State.pair zv1 zv2;
      upv     = State.pair up1 up2;
      lastx   = State.pair lv1 lv2;
      nextx   = State.pair xv1 xv2;
      diffx   = State.pair dx1 dx2;
      eqs     = State.pair eq1 eq2;
      eqs_env = Ident.Env.append eqs_env1 eqs_env2;
      locals  = Ident.S.union locals1 locals2;
      inits   = State.pair inits1 inits2;
      lastmap = Ident.Env.append lastmap1 lastmap2; }

let merge ss = List.fold_right pair ss empty

let solver_outputs acc ctx =
  let name (x, _) s = Ident.S.add x s in
  let r = State.fold name ctx.upv acc in
  let r = State.fold name ctx.nextx r in
  let r = State.fold name ctx.diffx r in
  r

let optional_with_ctx f = function
  | None -> None, empty
  | Some x ->
      let e, ctx = f x in
      Some e, ctx

(** make a pattern from a state of input variables *)
let extend_pat s p_list =
  let s_list = State.list [] s in
  let spat = 
    match s_list with
      | [] -> make(Ewildpat)
      | [(n, _)] -> make(Evarpat(n))
      | _ -> make(Etuplepat(List.map (fun (n, _) -> make (Evarpat(n))) s_list))
  in
  spat :: p_list

(** make an output expression complemented with a state vector *)
let exp_of_state s =
  let s_list = State.list [] s in
  match s_list with
    | [] -> val_unit
    | [(n, _)] -> local n
    | _ -> make(Etuple(List.map (fun (n, _) -> local n) s_list))

let typ_of_state s =
  let s_list = State.list [] s in
  match s_list with
    | [] -> Initial.typ_unit
    | [(_, ty)] -> ty
    | _ -> Types.make (Tproduct (List.map snd s_list))

(** Find the kind of a global identifier *)
let kind f =
  let { info = { value_typ = { typ_body = typ_body } } } =
    try Modules.find_value f
    with Not_found ->
      failwith (Printf.sprintf "Kind lookup of '%s' failed." (Lident.modname f))
  in
  match typ_body with
    | Tvalue _ -> Tany | Tsignature(k, _, _, _) -> k

let contfun_types f =
  let { info = { value_typ = tys } } = Modules.find_value f in
    match Types.instance_of_type_signature tys with
    |  _, _, ty_zv :: ty_lxv :: ty_arg_list,
       { t_desc = Tproduct [ty_res; ty_upv; ty_xv; ty_dxv]}
       -> ((ty_zv, ty_lxv), (ty_res, ty_upv, ty_xv, ty_dxv))
    | _ -> assert false

let pat_of_var_list l = make (Etuplepat(List.map (fun n -> make(Evarpat(n))) l))

(* TODO: handle automata, etc. and shift this into hybrid.ml *)
(* Return variables defined by equations (and visible 'at the top') *)
let
rec add_bound bound local =
  match local.l_desc with
  | Elocalvar id -> Ident.S.add id bound
  | Elocallet _ -> bound

(* Return der variables defined across a set of blocks, i.e. those visible from
   the top *)
(* TODO: it would be easy to replace this function once a mechanism for
         properly handling ders in let/in blocks is in place, since the
         continuous variables defined within a subexpression are then
         visible in the context returned from processing that subexpression.
 *)
let shallow_ders exclude blks =
  let add_bound_vars bound local =
    match local.l_desc with
    | Elocalvar id -> Ident.S.add id bound
    | Elocallet _ -> bound
  in
  let
  rec f_eq bound acc eq =
    match eq.desc with
    | Eder (x, _, _, _) when not (exclude x || Ident.S.mem x bound)
                      -> Ident.S.add x acc
    | Ematch (_, mhs) -> f_mhs bound acc mhs
    | Ereset (blk, _) -> f_blk bound acc blk
    | Epresent (p_h_list, b_opt) ->
        let acc = optional (f_blk bound) acc b_opt in
        List.fold_left (fun acc p_h -> f_blk bound acc p_h.p_block) acc p_h_list
    | Eautomaton s_h_list -> List.fold_left (f_sh bound) acc s_h_list
    | _ -> acc

  and f_mh bound acc mh = f_blk bound acc mh.m_block
  and f_mhs bound acc mh_list = List.fold_left (f_mh bound) acc mh_list

  and f_blk bound acc blk =
    let bound = List.fold_left add_bound_vars bound blk.b_locals in
    List.fold_left (f_eq bound) acc blk.b_eq

  and f_esc bound acc esc = List.fold_left (f_eq bound) acc esc.e_eq

  and f_sh bound acc { s_block = blk; s_until = until; s_unless = unless } =
    let acc = f_blk bound acc blk in
    let acc = List.fold_left (f_esc bound) acc until in
    List.fold_left (f_esc bound) acc unless

  in
  List.fold_left (f_blk empty_id_set) empty_id_set blks

(* TODO: extend to handle external nodes *)
(* Given the type of a dx or upv variable, return an expression, of that type,
   for suspending or initializing, respectively, that variable. *)
let rec suspend_var ty_dx =
  match ty_dx.t_desc with
  | Tproduct tys -> make (Etuple (List.map suspend_var tys))
  | Tconstr (l, _, _) when l = Initial.unit_ident  -> val_unit
  | Tconstr (l, _, _) when l = Initial.float_ident -> fval_zero
  | Tconstr (l, _, _) when l = Initial.bool_ident  -> val_false
  | _ -> assert false

(* Takes a context and returns a list of equations containing
   - for each x:      x  = last x
   - for each dx:     dx = suspend_var(dx)
   - for each u:      u  = last u

   NB: suspending a zero-crossing across a match/with requires introducing a
       memory to memorise the last value of the zero-crossing expression. *)
let suspend_ctx ctx =
  let persist (x, _) acc = make (Eeq (make (Evarpat x), make (Elast x))) :: acc
  and suspend (x, ty) acc = make (Eeq (make (Evarpat x), suspend_var ty)) :: acc
  and dontcare (x, ty) acc = make (Eeq (make (Evarpat x), fval_one)) :: acc
  in
  let eqs = State.fold persist ctx.nextx [] in
  let eqs = State.fold suspend ctx.diffx eqs in
  let eqs = State.fold dontcare ctx.upv eqs in  (* TODO: should be shared, not suspended *)
  eqs

(* The memory for each upv must be initialized somewhere, by adding:
            init upv = 0.0
   at the top-level (just inside the node), for each upv that has been
   suspended using last upv.

   Existing inits are ignored as the inits need only be calculated for the
   upper-most match/with constructs. This approach is perhaps a bit inefficient
   but it's simpler since we build the contexts from the inside out. *)
let recalculate_inits ctx =
  let init (x, ty) = make (Einit (make (Evarpat x), fval_one))
  in
  { ctx with inits = State.map init ctx.upv }

let complete_blks new_writes suspends blks =
  let f state blk =
    match state with
    | (rs, (lsusp, csusp::rsusp)) ->
        let eqs = List.flatten (lsusp :: rsusp) in
        let blk =
          { blk with
              b_eq = eqs @ blk.b_eq;
              b_write = Ident.S.union blk.b_write new_writes; }
        in
        (blk::rs, (csusp @ lsusp, rsusp))
    | _ -> assert false
  in
  let r, _ = List.fold_left f ([], ([], suspends)) blks in
  List.rev r

(** Translate an expression *)
let rec expression e =
  match e.desc with
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e, empty
 
  | Eapp (Eup, [e1]) ->
      (* up(e) produces - an equation upz = e - a new entry z --- *)
      (* an expression z *)
      let e1, ctx = expression e1 in
      let z = Ident.fresh "z" in
      let upz = Ident.fresh "upz" in
      { e with desc = Elocal(z) },
      { ctx with zero = State.cons (z, typ_bool) ctx.zero;
                 upv  = State.cons (upz, typ_float) ctx.upv;
                 eqs  = State.cons (make(Eeq(make(Evarpat(upz)), e1))) ctx.eqs;
                 eqs_env = env_add ctx.eqs_env (upz, typ_float);
      }

    (* NB: need to keep kind = Tcont even after hybrid translation *)
  | Eapp(Eop(lname) as op, e_list) when kind lname = Tcont ->
      let e_list, ctx = expression_list e_list in
      let z   = Ident.fresh "z" in
      let r   = Ident.fresh "r" in
      let upz = Ident.fresh "upz" in
      let lx  = Ident.fresh "lx" in
      let x   = Ident.fresh "x" in
      let dx  = Ident.fresh "dx" in
      (* (r, upz, x, dx) = op(z, lx, e1,...,en) *)
      let new_eq =
        make (Eeq(pat_of_var_list [r; upz; x; dx],
           { e with desc = Eapp(op, local z :: local lx :: e_list) }))
      in
      let ((ty_z, ty_lx), (ty_r, ty_upz, ty_x, ty_dx)) = contfun_types lname
      in
      { e with desc = Elocal(r) },
      { ctx with
          zero    = State.cons (z,   ty_z) ctx.zero;
          upv     = State.cons (upz, ty_upz) ctx.upv;
          lastx   = State.cons (lx,  ty_lx) ctx.lastx;
          nextx   = State.cons (x,   ty_x) ctx.nextx;
          diffx   = State.cons (dx,  ty_dx) ctx.diffx;
          eqs     = State.cons new_eq ctx.eqs;
          eqs_env = env_adds ctx.eqs_env
                      [(r, ty_r); (upz, ty_upz); (x, ty_x); (dx, ty_dx)];
      }

  | Eapp(op, e_list) ->
      let e_list, ctx = expression_list e_list in
      { e with desc = Eapp(op, e_list) }, ctx

  | Etuple(e_list) ->
      let e_list, ctx = expression_list e_list in
      { e with desc = Etuple(e_list) },
      ctx

  | Erecord_access(e1, label) ->
      let e1, ctx = expression e1 in
      { e with desc = Erecord_access(e1, label) }, ctx

  | Erecord(l_e_list) ->
      let l_e_list, ctx = record_list l_e_list in
      { e with desc = Erecord(l_e_list) }, ctx

  | Etypeconstraint(e1, ty) ->
      let e1, ctx = expression e in
      { e with desc = Etypeconstraint(e1, ty) }, ctx

  | Elet({ l_desc = Elocallet eqs; l_env = l_ctx }, e1) ->
      let ctx = equation_list eqs in
      let e1, ctx_e1 = expression e1 in
      let locals = Vars.defs eqs in
      e1, pair ctx (pair ctx_e1 ({ empty with eqs_env = l_ctx;
                                              locals = locals; }))

  | Elet(local, e1) -> assert false

  | Eseq(e1, e2) ->
      let e1, ctx1 = expression e1 in
      let e2, ctx2 = expression e2 in
      { e with desc = Eseq(e1, e2) }, pair ctx1 ctx2

  | Eperiod _ -> assert false

and record_list l_e_list =
  match l_e_list with
    | [] -> [], empty
    | (label, e) :: l_e_list ->
        let e, ctx = expression e in
        let l_e_list, ctx_l_e = record_list l_e_list in
        (label, e) :: l_e_list, pair ctx ctx_l_e

and expression_list e_list =
  match e_list with
    | [] -> [], empty
    | e :: e_list ->
        let e, ctx_e = expression e in
        let e_list, ctx = expression_list e_list in
        e :: e_list, pair ctx_e ctx

and equation eq = equation' (Ident.Env.empty, Ident.Env.empty) eq

and equation' (m_lx, m_dx) eq =
  match eq.desc with
  | Eeq(p, e) ->
      (* TODO: type p against e, and add to ctx.eqs_env,
               or, better to get this information from enclosing blocks,
               if possible *)
      let e, ctx = expression e in
      { ctx with eqs = State.cons { eq with desc = Eeq(p, e) } ctx.eqs }

    (* special case for ders defined across match/with branches *)
  | Eder(x, e, e0_opt, h) when Ident.Env.mem x m_lx ->
      let e, ctx = expression e in
      let e0_opt, ctx0 = optional_with_ctx expression e0_opt in
      let h, ctxh = handler h in
      let ctx = pair ctx (pair ctx0 ctxh) in
      let lx = Ident.Env.find x m_lx in
      let dx = Ident.Env.find x m_dx in
      let dx_eq = { eq with desc = Eeq(make(Evarpat(dx)), e) } in
      let x_eq  = { eq with desc =
        Eactivate(make(Evarpat(x)), h, Some(local lx), e0_opt) }
      in
      { ctx with eqs = State.cons x_eq (State.cons dx_eq ctx.eqs) }

  | Eder(x, e, e0_opt, h) ->
      let e, ctx = expression e in
      let e0_opt, ctx0 = optional_with_ctx expression e0_opt in
      let h, ctxh = handler h in
      let ctx = pair ctx (pair ctx0 ctxh) in
      let lx = Ident.fresh "lx" in
      let dx = Ident.fresh "dx" in
      let dx_eq = { eq with desc = Eeq(make(Evarpat(dx)), e) } in
      let x_eq  = { eq with desc =
        Eactivate(make(Evarpat(x)), h, Some(local lx), e0_opt) }
      in
      { ctx with eqs     = State.cons x_eq (State.cons dx_eq ctx.eqs);
                 eqs_env = env_add ctx.eqs_env (dx, typ_float);
                 lastx   = State.cons (lx, typ_float) ctx.lastx;
                 nextx   = State.cons (x,  typ_float) ctx.nextx;
                 diffx   = State.cons (dx, typ_float) ctx.diffx;
                 lastmap = Ident.Env.add x lx ctx.lastmap }

  | Eactivate(p, h, e_opt, e0_opt) ->
      let e_opt, ctx = optional_with_ctx expression e_opt in
      let e0_opt, ctx0 = optional_with_ctx expression e0_opt in
      let h, ctxh = handler h in
      let ctx = pair ctx (pair ctx0 ctxh) in
      let new_eq =
        { eq with desc = Eactivate(p, h, e_opt, e0_opt) } in    
      (* TODO: type p against e, and add to ctx.eqs_env
               or, better to get this information from enclosing blocks,
               if possible *)
      { ctx with eqs = State.cons new_eq ctx.eqs }

  | Einit (p, e) ->
      let e, ctx = expression e in
      let new_eq = { eq with desc = Einit(p, e) } in
      (* TODO: type p against e, and add to ctx.eqs_env
               or, better to get this information from enclosing blocks,
               if possible *)
      { ctx with eqs = State.cons new_eq ctx.eqs }

  | Ematch (e, m_h_list) ->
      let e, ctx = expression e in
      let make_new_eq blks =
        let m_h_list =
          List.map2 (fun m_h blk -> { m_h with m_block = blk }) m_h_list blks
        in
        make (Ematch (e, m_h_list))
      in
      pair ctx
        (exclusive_blocks
           make_new_eq
           (m_lx, m_dx)
           (List.map (fun m_h -> m_h.m_block) m_h_list))

  | Ereset (blk, e) ->
      let e, ctx = expression e in
      let blk, blk_ctx = block' (m_lx, m_dx) blk in
      let blk_ctx =
        { blk_ctx with eqs = State.singleton (make (Ereset (blk, e))) }
      in
      pair ctx blk_ctx

  (* These cases are only activated when Misc.ex_der_auto = true *)

  | Eemit (x, e_opt) ->
      let e_opt, ctx = optional_with_ctx expression e_opt in
      { ctx with eqs = State.cons { eq with desc = Eemit(x, e_opt) } ctx.eqs }

  | Epresent (p_h_list, b_opt) -> (* TODO: needs work *)
      let fblock (ctx, blist) ({ p_block = blk } as p_h) =
        let blk, blk_ctx = block' (m_lx, m_dx) blk in
        pair ctx blk_ctx, { p_h with p_block = blk } :: blist
      in
      let b_opt, d_ctx = optional_with_ctx (block' (m_lx, m_dx)) b_opt in
      let ctx, p_h_list_r = List.fold_left fblock (d_ctx, []) p_h_list in
      { ctx with eqs = State.cons
                        { eq with desc = Epresent (List.rev p_h_list_r, b_opt) }
                        ctx.eqs }

  | Eautomaton s_h_list ->
      (* TODO:
         - should descend into s_until and s_unless e_next_state expressions.
           This will require proper handling for let/in expressions (i.e. they
           must not be flattened).
           see the rough state_handler and escape functions sketched out in a
           comment below.
         - internal up()s may require special handling as per discussion with
           Marc 25/4/2011 (i.e. add additional delronds).
         - will need special handling for reset expressions (i.e. the
           escape.e_eq lists in s_until and s_unless) on continuous variables.
       *)
      let make_new_eq blks =
        let s_h_list =
          List.map2 (fun s_h blk -> { s_h with s_block = blk }) s_h_list blks
        in make (Eautomaton s_h_list)
      in
      exclusive_blocks make_new_eq (m_lx, m_dx)
        (List.map (fun s_h -> s_h.s_block) s_h_list)

and equation_list eq_list =
  equation_list' (Ident.Env.empty, Ident.Env.empty) eq_list

and equation_list' m = function
  | [] -> empty
  | eq :: eq_list ->
      let ctx_eq = equation' m eq in
      let ctx = equation_list' m eq_list in
      pair ctx_eq ctx

and exclusive_blocks make_new_eq (m_lx, m_dx) blks =

  (* cstate variables introduced from branching at a higher level *)
  let introduced_earlier x = Ident.Env.mem x m_lx in

  (* cstate variables to be managed across branches at this level *)
  let shared_ders = shallow_ders introduced_earlier blks in

  (* Augment m_lx and m_dx with mappings for the shared_ders *)
  let m_lx = Ident.Env.append m_lx (Ident.S.fresh "lx" shared_ders) in
  let m_dx = Ident.Env.append m_dx (Ident.S.fresh "dx" shared_ders) in

  (* dx variables introduced at this level *)
  let diffx = Ident.S.map (fun x -> Ident.Env.find x m_dx) shared_ders in

  (* Descend into each block, merge the resulting contexts, but
     ignore the equations at this point as they will be later added as part
     of a single Ematch/Eautomaton equation (after suspends have been
     introduced) *)
  let blks, ctxs = List.split (List.map (block' (m_lx, m_dx)) blks) in
  let ctx = { (merge ctxs) with eqs = State.empty } in

  (* Introduce suspension equations for local cstate and zeroc variables.
     We pass diffx as a list of additional variables that are written, there
     is no need to pass shared_ders because we assume that they are already
     present in each branch, TODO: we should probably also pass zero-crossing
     variables that are changed. *)
  let suspends = List.map suspend_ctx ctxs in
  let blks = complete_blks diffx suspends blks in
  let new_eq = make_new_eq blks in

  (* Add declarations for new variables introduced at this level *)
  let nextx = Ident.S.fold (fun x r -> (x, typ_float) ::r) shared_ders [] in
  let lastx = List.map (fun (x, ty) -> (Ident.Env.find x m_lx, ty)) nextx
  and diffx = Ident.S.fold (fun x r -> (x, typ_float) ::r) diffx []

  in
  { (recalculate_inits ctx) with
      nextx = State.cons_list nextx ctx.nextx;
      lastx = State.cons_list lastx ctx.lastx;
      diffx = State.cons_list diffx ctx.diffx;

      eqs = State.cons new_eq ctx.eqs;
      eqs_env = List.fold_left env_adds ctx.eqs_env [nextx; lastx; diffx];

      lastmap = Ident.Env.append ctx.lastmap m_lx; }

and block' m ({ b_locals = b_locals; b_eq = b_eq } as blk) =
  (* shift all let equations into the main set of equations; hiding their
     names instead with local. *)
  (* TODO: this has to be done differently if structure of lets, i.e the order
     of definitions is to be preserved. *)
  let flatten_eq (eqs, env, locals) { l_desc = l_desc; l_env = l_env } =
    let env = Ident.Env.append env l_env in
    match l_desc with
    | Elocallet leqs -> (leqs @ eqs, env, Vars.defs leqs)
    | Elocalvar id   -> (eqs,        env, Ident.S.add id locals)
  in

  let eq_list, l_eqs_env, locals =
    List.fold_left flatten_eq (b_eq, Ident.Env.empty, empty_id_set) b_locals
  in

  let lctx = { empty with locals = locals; eqs_env = l_eqs_env } in
  let ctx = pair (equation_list' m eq_list) lctx in

  (* continuous state variables are not made local, because they must be
     returned by the function *)
  let xset = State.fold (fun (x, _) -> Ident.S.add x) ctx.nextx empty_id_set in
  let make_local id r =
    if Ident.S.mem id xset then r
    else
      let env =
        try
          Ident.Env.add id (Ident.Env.find id ctx.eqs_env) Ident.Env.empty
        with Not_found -> Ident.Env.empty
      in
      { l_desc = Elocalvar id; l_env = env; l_loc = Location.no_location } :: r
  in

  (* rebuild the block from the generated context hiding local (non c-state)
     valiables. *)
  let blk = { blk with b_locals = Ident.S.fold make_local ctx.locals [];
                       b_eq = State.list [] ctx.eqs;
                       b_write = solver_outputs blk.b_write ctx; }
  in
  blk, { ctx with locals = empty_id_set }

and handler = function
  | [] -> [], empty
  | (e, ez) :: h ->
      (* we leave e unchanged as it is necessarily discrete *)
      let ez, ctx_ez = expression ez in
      let h, ctx = handler h in 
      (e, ez) :: h, pair ctx_ez ctx

(*
and state_handler m ({ s_block = b; s_until = e_l1; s_unless = e_l2 } as s_h) =
  let blk, ctx = block' m b in
  and e_l1, ctx = List.fold_left escape ctx e_l1 in
  and e_l2, ctx = List.fold_left escape ctx e_l2 in
  { s_h with s_block = b; s_until = e_l1; s_unless = e_l2 }, ctx

and escape m ({ e_eq = eqs; e_next_state = next } as escape) =
  let next, ctx =
    match next with
    | Estate0 _ -> next, empty
    | Estate1 (id, e_list) ->
        let e_list, ctx = expression_list in
        (* XXX TODO XXX *)
  in
  { escape with e_eq = eqs; e_next_state = next }
*)

let filter_lasts ids =
  let fl e = match e with
    | Elast x ->
        (try Elocal (Ident.Env.find x ids)
         with Not_found -> e)
    | _ -> e
  in
  filter_leaves fl

let make_let eqs eqs_env e =
  match eqs with
  | [] -> e
  | _  ->
      let local =
        { l_desc = Elocallet eqs;
          l_env  = eqs_env;
          l_loc  = Location.no_location; }
      in
      make (Elet (local, e))

let reset_last (x, _) env0 =
  let tentry = Ident.Env.find x env0 in
  tentry.t_sort <- Val;
  env0

let implementation impl =
  match impl.desc with
    | Efundecl(f, k, p_list, e) ->
      if k = C then
        let e, { zero = z; upv = upv; lastx = lx; nextx = x; diffx = dx;
                 eqs = eqs; eqs_env = eqs_env; inits = inits;
                 lastmap = lastmap }
          = expression e
        in
        let p_list = extend_pat z (extend_pat lx p_list)
        in
        let e = make_let
            (State.list (State.list [] eqs) inits)
            (State.fold reset_last x eqs_env)
            (make (Etuple [e;
              exp_of_state upv; exp_of_state x; exp_of_state dx]))
        in
        let e = filter_lasts lastmap e in

        (* typing *)
        let { info = f_tys } = Modules.find_value (Lident.Name f) in
        let typ_body =
          match Types.instance_of_type_signature f_tys.value_typ with
          | Tcont, safe, ty_arg_list, ty_res ->
              let ty_res =
                Types.make
                  (Tproduct [ty_res; typ_of_state upv;
                             typ_of_state x; typ_of_state dx])
              in
              Tsignature (Tcont, safe,
                typ_of_state z :: typ_of_state lx :: ty_arg_list, ty_res)
          | _ -> assert false
        in
        Modules.update_value f
          { f_tys with value_typ = { f_tys.value_typ with typ_body = typ_body }};

        (* result *)
        { impl with desc = Efundecl (f, D, p_list, e) }
      else impl
    | _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Generate simulation stubs *)

let filter_fun_types ty_args ty_res =
  match ty_args with
  | ty_zv :: ty_lxv :: ty_args ->
    (match ty_res with
     | { t_desc = Tproduct [ty_res; ty_upv; ty_xv; ty_dxv] } -> ty_args, ty_res
     | _ -> assert false)
  | _ -> assert false

let filter_hy_types ty_args ty_res =
  match ty_args with
  | ty_zv :: ty_lxv :: ty_args ->
    (match ty_res with
     | { t_desc = Tproduct [ty_res; ty_upv; ty_xv; ty_dxv] } ->
         (ty_zv, ty_lxv), (ty_upv, ty_xv, ty_dxv)
     | _ -> assert false)
  | _ -> assert false

let state_tallies info =
  let { info = { value_typ = tys } } = info in
  let _, _, ty_args, _ = Types.instance_of_type_signature tys in
  match ty_args with
  | ty_zv :: ty_lxv :: ty_args -> (typ_to_ctally ty_lxv, typ_to_ctally ty_zv)
  | _ -> assert false

open Obc
let omake = make

let print_main ff qualid fname =
  let { info = { value_typ = tys } } =
    Modules.find_value (Lident.Modname(qualid))
  in
  let _, _, ty_args, ty_res = Types.instance_of_type_signature tys in
  let (ty_zv, ty_lxv), (ty_upv, ty_xv, ty_dxv) = filter_hy_types ty_args ty_res
  in

  let zv  = Ident.fresh "zv"
  and xv  = Ident.fresh "xv"
  and upv = Ident.fresh "upv"
  and dxv = Ident.fresh "dxv"
  and mem = Ident.fresh "mem"
  and dis = Ident.fresh "d"
  in
  let zv_arg = flatten_typ_arg zv ty_zv
  and xv_arg = flatten_typ_arg xv ty_lxv
  and upv_vars, upv_pat = flatten_typ_pat "u" ty_upv
  and xv_vars,  xv_pat  = flatten_typ_pat "x" ty_dxv
  and dxv_vars, dxv_pat = flatten_typ_pat "d" ty_dxv
  and add_step_suffix qid =
    { qid with Lident.id = qid.Lident.id ^ "_step" }
  in

  let unit_arg = omake (Oconst Ovoid) in
  let lhs =
    omake (Otuplepat [omake Owildpat; upv_pat; xv_pat; dxv_pat]) in
  let step_call = omake
    (Oapp (Lident.Modname (add_step_suffix qualid),
      [omake (Olocal (mem, Obc.Val)); zv_arg; xv_arg; unit_arg]))
  in
  let do_nothing = omake (Oconst Ovoid) in
  (* create a sequence of array assignments to dx: *)
  (*   dxv[0] <- dxv *)
  let copy_to_dx = assign_from_vars dxv dxv_vars do_nothing in
  let copy_to_x = assign_from_vars xv xv_vars do_nothing in
  let blit_if = omake (
    Oifthenelse (omake (Olocal (dis, Obc.Val)),
                 copy_to_x,
                 copy_to_dx))
  in
  let copy_vars = assign_from_vars upv upv_vars blit_if in
  let main_body = omake (Olet ([(lhs, step_call)], copy_vars)) in

  let makearg id = omake (Ovarpat id) in
  let main = omake
    (Oletfun
      ("main",
       [omake (Otuplepat (List.map makearg [xv; dxv; upv; zv; dis]))],
       main_body))
  in
  let init = omake
    (Oletvalue (Ident.name mem,
                omake (Oapp (Lident.Modname qualid, []))))
  in

  Modules.initialize "__Main";
  Oprinter.implementation_list ff false [init; main];

