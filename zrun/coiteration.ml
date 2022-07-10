(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* An Operational Semantics for Zelus *)
(* This is based on a companion file and working notes on the co-iterative *)
(* semantics presented at the SYNCHRON workshop, December 2019, *)
(* the class on "Advanced Functional Programming" given at Bamberg
   Univ. in June-July 2019 and the Master MPRI - M2, Fall 2019, 2020, 2021 *)
(* The original version of this code is taken from the GitHub Zrun repo: *)
(* https://github.com/marcpouzet/zrun *)
(* Zrun was programmed right after the COVID black out, in June 2020 *)
(* This new version includes Zelus constructs: ODEs and zero-crossing; *)
(* higher order functions; the implem. was done in 2021 and updated in 2022 *)
open Smisc
open Error
open Monad
open Opt                                                            
open Result
open Ident
open Genv
open Find
open Zelus
open Value
open Primitives
open Match
open Sdebug
   
(* evaluation functions *)

(* [reset init step genv env body s r] resets [step genv env body] *)
(* when [r] is true *)
let reset init step genv env body s r =
  let*s = if r then init genv env body else return s in
  step genv env body s

(* Pattern matching *)
let imatch_handler ibody genv env { m_body } =
  ibody genv env m_body
  
let smatch_handler_list loc sbody genv env ve m_h_list s_list =
  let rec smatch_rec m_h_list s_list =
    match m_h_list, s_list with
    | [], [] -> error { kind = Epattern_matching_failure; loc = loc }
    | { m_pat; m_body } :: m_h_list, s :: s_list ->
       let r = Match.pmatch ve m_pat in
       let* r, s =
         match r with
         | None ->
            (* this is not the good handler; try an other one *)
            let* r, s_list =
              smatch_rec m_h_list s_list in
            return (r, s :: s_list)
         | Some(env_pat) ->
            let env_pat = liftv env_pat in
            let env = Env.append env_pat env in
            let* r, s = sbody genv env m_body s in
            return (r, s :: s_list) in
       return (r, s)
    | _ -> error { kind = Estate; loc = loc } in
  smatch_rec m_h_list s_list

(* Present handler *)
let ipresent_handler iscondpat ibody genv env { p_cond; p_body } =
  let* sc = iscondpat genv env p_cond in
  let* sb = ibody genv env p_body in
  return (Stuple [sc; sb])

let idefault_opt ibody genv env default_opt =
  match default_opt with
  | Init(b) -> ibody genv env b
  | Else(b) -> ibody genv env b
  | NoDefault -> return Sempty

let spresent_handler_list loc sscondpat bot nil sbody genv env p_h_list s_list =
  let rec spresent_rec p_h_list s_list =
    match p_h_list, s_list with
    | [], [] ->
       return (Opt.none, []) (* no condition is true *)
    | { p_cond; p_body; p_loc } :: p_h_list, Stuple [s_cond; s_body] :: s_list ->
       let* (r, env_pat), s_cond = sscondpat genv env p_cond s_cond in
       let* r, s =
         match r with
         | Vbot ->
            return (Opt.return bot, Stuple [s_cond; s_body] :: s_list)
         | Vnil ->
            return (Opt.return nil, Stuple [s_cond; s_body] :: s_list)
         | Value(v) ->
            let* v =
              Opt.to_result ~none:{ kind = Etype; loc = p_loc } (bool v) in
            if v then
              (* this is the good handler *)
              let env = Env.append env_pat env in
              let* r, s_body = sbody genv env p_body s_body in
              return (Opt.return r, Stuple [s_cond; s_body] :: s_list)
            else
              let* r, s_list = spresent_rec p_h_list s_list in
              return (r, Stuple [s_cond; s_body] :: s_list) in
       return (r, s)
    | _ -> error { kind = Estate; loc = loc } in
  spresent_rec p_h_list s_list

(* [sem genv env e = CoF f s] such that [iexp genv env e = s] *)
(* and [sexp genv env e = f] *)
let rec iexp genv env { e_desc; e_loc  } =
  match e_desc with
  | Econst _ | Econstr0 _ | Elocal _ | Eglobal _ | Elast _ ->
     return Sempty
  | Econstr1 { arg_list } ->
     let* s_list = map (iexp genv env) arg_list in
     return (Stuple(s_list))
  | Eop(op, e_list) ->
     begin match op, e_list with
     | Efby, [{ e_desc = Econst(v) }; e] ->
        (* synchronous register initialized with a static value *)
        let* s = iexp genv env e  in
        return (Stuple [Sval(Value (Combinatorial.immediate v)); s])
     | Efby, [e1; e2] ->
        let* s1 = iexp genv env e1 in
        let* s2 = iexp genv env e2 in
        return (Stuple [Sopt(None); s1; s2])
     | Eunarypre, [e] -> 
        (* un-initialized synchronous register *)
        let* s = iexp genv env e in
        return (Stuple [Sval(Vnil); s])
     | Eminusgreater, [e1; e2] ->
        let* s1 = iexp genv env e1 in
        let* s2 = iexp genv env e2 in
        return (Stuple [Sval(Value(Vbool(true))); s1; s2])
     | Eifthenelse, [e1; e2; e3] ->
        let* s1 = iexp genv env e1 in
        let* s2 = iexp genv env e2 in
        let* s3 = iexp genv env e3 in
        return (Stuple [s1; s2; s3])
     | Eseq, [e1; e2] ->
        let* s1 = iexp genv env e1 in
        let* s2 = iexp genv env e2 in
        return (Stuple [s1; s2])
     | Erun _, [{ e_loc } as e1; e2] ->
        (* node instanciation. [e1] must be a static expression *)
        let* v = Combinatorial.exp genv env e1 in          
        let* v = Primitives.pvalue v |>
                   Opt.to_result ~none: { kind = Etype; loc = e_loc} in
        let* v =
          Primitives.get_node v |>
            Opt.to_result ~none: { kind = Eshould_be_a_node; loc = e_loc} in
        let* si = instance v in
        let* s2 = iexp genv env e2 in
        return (Stuple [Sinstance(si); s2])
     | (Eatomic | Etest | Edisc), [e] ->
        iexp genv env e
     | Eup, [e] ->
        let* s = iexp genv env e in
        return
          (Stuple [Szstate { zin = false; zout = max_float }; s])
     | Eperiod, [e1; e2] ->
        (* [e1] and [e2] must be static *)
        let* v1 = Combinatorial.exp genv env e1 in
        let* v2 = Combinatorial.exp genv env e2 in
        let* v1 = vfloat v1 |>
                    Opt.to_result ~none: { kind = Etype; loc = e_loc} in
        let* v2 = vfloat v2 |>
                    Opt.to_result ~none: { kind = Etype; loc = e_loc} in
        return
          (Speriod
             { zin = false; phase = v1; period = v2; horizon = v1 +. v2 })
     | (Econcat | Eget), [e1; e2] ->
        let* s1 = iexp genv env e1 in
        let* s2 = iexp genv env e2 in
        return (Stuple [s1; s2])
     | (Eget_with_default | Eslice | Eupdate), [e1; e2; e3] ->
        let* s1 = iexp genv env e1 in
        let* s2 = iexp genv env e2 in
        let* s3 = iexp genv env e3 in
        return (Stuple [s1; s2; s3])
     | _ -> error { kind = Etype; loc = e_loc }
     end
  | Etuple(e_list) -> 
     let* s_list = map (iexp genv env) e_list in
     return (Stuple(s_list))
  | Eapp({ e_desc = Eglobal { lname } }, e_list) ->
     (* When [e] is a global value, it can denote either a *)
     (* combinatorial function or a node; otherwise, [e] must be *)
     (* combinatorial *)
     let* s_list = map (iexp genv env) e_list in
     let* v =
       find_gvalue_opt lname genv |>
         Opt.to_result ~none: { kind = Eunbound_lident(lname); loc = e_loc} in
     let* s =
       match v with
       | Vclosure ({ c_funexp = { f_kind = Knode | Khybrid } } as c) ->
          let* si = instance c in
          return (Sinstance(si))
       | _ -> return Sempty in
     return (Stuple(s :: s_list))
  | Eapp(e, e_list) ->
     let* s = iexp genv env e in
     let* s_list = map (iexp genv env) e_list in
     return (Stuple(s :: s_list))
  | Elet(leq, e) ->
     let* s_eq = ileq genv env leq in
     let* se = iexp genv env e in
     return (Stuple [s_eq; se])
  | Erecord_access({ arg }) ->
     iexp genv env arg
  | Erecord(r_list) ->
     let* s_list = map (fun { arg } -> iexp genv env arg) r_list in
     return (Stuple(s_list))
  | Erecord_with(e, r_list) ->
     let* se = iexp genv env e in
     let* s_list = map (fun { arg } -> iexp genv env arg) r_list in
     return (Stuple(se :: s_list))
  | Etypeconstraint(e, _) -> iexp genv env e
  | Efun _ -> return Sempty
  | Ematch { e; handlers } ->
     let* se = iexp genv env e in
     let* s_handlers = map (imatch_handler iexp genv env) handlers in
     return (Stuple (se :: s_handlers))
  | Epresent { handlers; default_opt } ->
     let* s_handlers =
       map (ipresent_handler iscondpat iexp genv env) handlers in
     let* s_default_opt = idefault_opt iexp genv env default_opt in
     return (Stuple (s_default_opt :: s_handlers))
  | Ereset(e_body, e_res) ->
     let* s_body = iexp genv env e_body in
     let* s_res = iexp genv env e_res in
     (* TODO: double the state; an idea from Louis Mandel *)
     (* in case of a reset, simply restart from this copy *)
     (* alternatively, the current solution recalls [iexp] *)
     (* in the actual, imperative implementation, generated code is *)
     (* statically scheduled and reset is obtained *)
     (* by executing a reset method which restores the state *)
     (* to its initial value *)
     return (Stuple[s_body; s_res])
  | Eassert(e_body) ->
     let* s_body = iexp genv env e_body in
     return s_body
  | Eforloop({ for_size; for_kind; for_index; for_body }) ->
     (* [for_size] must be a static expression *)
     let* v = Combinatorial.exp genv env for_size in          
     let* v = Primitives.pvalue v |>
                Opt.to_result ~none: { kind = Etype; loc = e_loc} in
     let* v =
       Primitives.int v |>
         Opt.to_result ~none: { kind = Etype; loc = e_loc} in
     let* s_kind = ifor_kind genv env for_kind in
     let* si_list = map (ifor_index genv env) for_index in
     let* s_result = ifor_result genv env for_body in
     (* the initial state is an array [s^n] where [n] is the size *)
     return (Stuple (Sval(Value(Vint(v))) :: s_kind ::
                       Sarray (Array.make v s_result) :: si_list))

and ifor_kind genv env for_kind =
  match for_kind with
  | Kforall -> return Sempty
  | Kforward(e_opt) ->
     match e_opt with | None -> return Sempty | Some(e) -> iexp genv env e

and ifor_index genv env { desc; loc } =
  match desc with
  | Einput(_, e, e_opt) ->
     let* se = iexp genv env e in
     let* se_opt =
       match e_opt with | None -> return Sempty | Some(e) -> iexp genv env e in
     return (Stuple [se; se_opt])
  | Eindex(_, e1, e2) ->
     let* s1 = iexp genv env e1 in
     let* s2 = iexp genv env e2 in
     return (Stuple [s1; s2])

and ifor_result genv env r =
  match r with
  | Forexp(e) -> iexp genv env e
  | Forreturns(v_list, b) ->
     let* s_v_list = map (ivardec genv env) v_list in
     let* s_b = ifor_block_initialize genv env b in
     return (Stuple (s_b :: s_v_list))

and ifor_block_initialize genv env { for_block; for_initialize } =
  let* s_b = iblock genv env for_block in
  let* s_i_list = map (ifor_initialize genv env) for_initialize in
  return (Stuple (s_b :: s_i_list))

and ifor_initialize genv env { desc = { last_exp } } =
  iexp genv env last_exp
  
and ieq genv env { eq_desc; eq_loc  } =
  match eq_desc with
  | EQeq(_, e) -> iexp genv env e
  | EQder(x, e, e0_opt, p_h_list) ->
     (* [x becomes an input; x' an output] *)
     (* they are stored as a state [x';x] *)
     let* se = iexp genv env e in
     let* s0 =
       match e0_opt with
       | None -> return Sempty | Some(e0) -> iexp genv env e0 in
     let* sp_h_list =
       map (ipresent_handler iscondpat iexp genv env) p_h_list in
     return
       (Stuple
          (Scstate { pos = zero_float; der = zero_float } ::
             se :: s0 :: sp_h_list))
  | EQinit(_, e) ->
     let* se = iexp genv env e in
     return (Stuple [Sopt(None); se])
  | EQemit(x, e_opt) ->
     let* s =
       match e_opt with
       | None -> return Sempty | Some(e) -> iexp genv env e in
     return s
  | EQif(e, eq1, eq2) ->
     let* se = iexp genv env e in
     let* seq1 = ieq genv env eq1 in
     let* seq2 = ieq genv env eq2 in
     return (Stuple [se; seq1; seq2])
  | EQand(eq_list) ->
     let* seq_list = map (ieq genv env) eq_list in
     return (Stuple seq_list)
  | EQlocal(b_eq) ->
     let* s_b_eq = iblock genv env b_eq in
     return s_b_eq
  | EQlet(leq, eq) ->
     let* s_leq = ileq genv env leq in
     let* s_eq = ieq genv env eq in
     return (Stuple [s_leq; s_eq])
  | EQreset(eq, e) ->
     let* s_eq = ieq genv env eq in
     let* se = iexp genv env e in
     return (Stuple [s_eq; se])
  | EQpresent { handlers; default_opt } ->
     let* s_list =
       map (ipresent_handler iscondpat ieq genv env) handlers in
     let* s_default_opt = idefault_opt ieq genv env default_opt in
     return (Stuple (s_default_opt :: s_list))
  | EQautomaton { handlers; state_opt } ->
     let* s_list = map (iautomaton_handler genv env) handlers in
     (* The initial state is the first in the list *)
     (* if no initialisation code is given *)
     let* a_h =
       List.nth_opt handlers 0 |>
         Opt.to_result ~none:{ kind = Eunexpected_failure; loc = eq_loc } in
     let* i, si = initial_state_of_automaton genv env a_h state_opt in
     (* two state variables: initial state of the automaton and reset bit *)
     return (Stuple(i :: Sval(Value(Vbool(false))) :: si :: s_list))
  | EQmatch { e; handlers } ->
     let* se = iexp genv env e in
     let* sm_list = map (imatch_handler ieq genv env) handlers in
     return (Stuple (se :: sm_list))
  | EQempty -> return Sempty
  | EQassert(e) ->
     let* se = iexp genv env e in
     return se
  | EQforloop({ for_size; for_kind; for_index; for_body = (_, f_b) }) ->
     (* [for_size] must be a static expression *)
     let* v = Combinatorial.exp genv env for_size in          
     let* v = Primitives.pvalue v |>
                Opt.to_result ~none: { kind = Etype; loc = eq_loc} in
     let* v =
       Primitives.int v |>
         Opt.to_result ~none: { kind = Etype; loc = eq_loc} in
     let* s_kind = ifor_kind genv env for_kind in
     let* si_list = map (ifor_index genv env) for_index in
     let* s_b = ifor_block_initialize genv env f_b in
     (* the initial state is an array [s^n] of size [n] *)
     return (Stuple (Sval(Value(Vint(v))) :: s_kind ::
                       Sarray(Array.make v s_b) :: si_list))

and iblock genv env { b_vars; b_body; b_loc  } =
  let* s_b_vars = map (ivardec genv env) b_vars in
  let* s_b_body = ieq genv env b_body in
  return (Stuple (s_b_body :: s_b_vars))
  
and ivardec genv env { var_init; var_default; var_loc; var_is_last } =
  let* s_init =
    match var_init with
    | None -> return (if var_is_last then Sval(Vnil) else Sempty)
    | Some(e) ->
       (* a state is necessary to store the previous value *)
       let* s = iexp genv env e in return (Stuple [Sopt(None); s]) in
  let* s_default =
    match var_default with
    | None -> return Sempty
    | Some(e) -> iexp genv env e in
  return (Stuple [s_init; s_default])
  
and iautomaton_handler genv env { s_let; s_body; s_trans; s_loc } =
  let* s_list = map (ileq genv env) s_let in
  let* s_body = iblock genv env s_body in
  let* st_list = map (iescape genv env) s_trans in
  return (Stuple [Stuple(s_list); s_body; Stuple(st_list)])
  
and ileq genv env { l_eq } = ieq genv env l_eq
                           
(* initial state of an automaton *)
and initial_state_of_automaton genv env { s_state = { desc; loc } } state_opt =
  match state_opt with
  | None ->
     (* no initial state is given. The initial state is the first *)
     (* in the list *)
     let* i = match desc with
       | Estate0pat(f) -> return (Sval(Value(Vstate0(f))))
       | Estate1pat(f, _) ->
          error { kind = Einitial_state_with_parameter(f); loc = loc } in
     return (i, Sempty)
  | Some(state) ->
     let* s = istate genv env state in
     return (Sopt(None), s)
  
and iescape genv env { e_cond; e_let; e_body; e_next_state; e_loc } =
  let* s_cond = iscondpat genv env e_cond in
  let* s_list = map (ileq genv env) e_let in
  let* s_body = iblock genv env e_body in
  let* s_state = istate genv env e_next_state in
  return (Stuple [s_cond; Stuple(s_list); s_body; s_state])
  
and iscondpat genv env { desc; loc } =
  match desc with
  | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
     let* s1 = iscondpat genv env sc1 in
     let* s2 = iscondpat genv env sc2 in
     return (Stuple [s1; s2])
  | Econdexp(e_cond) ->
     iexp genv env e_cond
  | Econdpat(e, p) ->
     let* se = iexp genv env e in
     return se
  | Econdon(sc, e) ->
     let* s_sc = iscondpat genv env sc in
     let* se = iexp genv env e in
     return (Stuple [s_sc; se])
  
and istate genv env { desc; loc } =
  match desc with
  | Estate0 _ -> return Sempty
  | Estate1(_, e_list) ->
     let* s_list = map (iexp genv env) e_list in
     return (Stuple(s_list))
  | Estateif(e, s1, s2) ->
     let* se = iexp genv env e in
     let* se1 = istate genv env s1 in
     let* se2 = istate genv env s2 in
     return (Stuple[se; se1; se2])
  
and iresult genv env { r_desc; r_loc } =
  match r_desc with
  | Exp(e) -> iexp genv env e
  | Returns(b) -> iblock genv env b

and instance ({ c_funexp = { f_args; f_body; f_loc }; c_genv; c_env } as c) =
  match f_args with
  | [ arg ] ->
     let* s_list = map (ivardec c_genv c_env) arg in
     let* s_body = iresult c_genv c_env f_body in
     return { init = Stuple (s_body :: s_list); step = c }
  | _ -> error { kind = Etype; loc = f_loc }
  
(* an iterator *)
let slist loc genv env sexp e_list s_list =
  let rec slist_rec e_list s_list =
    match e_list, s_list with
    | [], [] -> return ([], [])
    | e :: e_list, s :: s_list ->
       let* v, s = sexp genv env e s in
       let* v_list, s_list = slist_rec e_list s_list in
       return (v :: v_list, s :: s_list)
    | _ ->
       error { kind = Estate; loc = loc } in
  slist_rec e_list s_list

(* The main step function *)
(* the value of an expression [e] in a global environment [genv] and local *)
(* environment [env] is a step function. *)
(* Its type is [state -> (value * state) option] *)
let rec sexp genv env { e_desc; e_loc } s =
  match e_desc, s with   
  | Econst(v), s ->
     return (Value (Combinatorial.immediate v), s)
  | Econstr0 { lname }, s ->
     return (Value (Vconstr0(lname)), s)
  | Elocal x, s ->
     let* v =
       find_value_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = e_loc } in
     return (v, s)
  | Eglobal { lname }, s ->
     let* v =
       find_gvalue_opt lname genv |>
         Opt.to_result ~none:{ kind = Eunbound_lident(lname); loc = e_loc } in
     return (Value(v), s)
  | Elast x, s ->
     let* v =
       find_last_opt x env  |>
         Opt.to_result ~none:{ kind = Eunbound_last_ident(x); loc = e_loc } in
     return (v, s)
  | Eop(op, e_list), s ->
     begin match op, e_list, s with
     | (* initialized unit-delay with a constant *)
       Efby, [_; e2], Stuple [Sval(v); s2] ->
        let* v2, s2 = sexp genv env e2 s2  in
        return (v, Stuple [Sval(v2); s2])
     | Efby, [e1; e2], Stuple [Sopt(v_opt); s1; s2] ->
        let* v1, s1 = sexp genv env e1 s1  in
        let* v2, s2 = sexp genv env e2 s2  in
        (* is-it the first instant? *)
        let v =
          match v_opt with | None -> v1 | Some(v) -> v in
        return (v, Stuple [Sopt(Some(v2)); s1; s2])
     | Eunarypre, [e], Stuple [Sval(v); s] -> 
        let* ve, s = sexp genv env e s in
        return (v, Stuple [Sval(ve); s])
     | Eminusgreater, [e1; e2], Stuple [Sval(v); s1; s2] ->
        (* when [v = true] this is the very first instant. [v] is a reset bit *)
        let* v1, s1 = sexp genv env e1 s1  in
        let* v2, s2 = sexp genv env e2 s2  in
        let* v_out =
          Primitives.ifthenelse v v1 v2 |>
            Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
        return (v_out, Stuple [Sval(Value(Vbool(false))); s1; s2])
     | Eifthenelse, [e1; e2; e3], Stuple [s1; s2; s3] ->
        let* v1, s1 = sexp genv env e1 s1 in
        let* v2, s2 = sexp genv env e2 s2 in
        let* v3, s3 = sexp genv env e3 s3 in
        let* v =
          ifthenelse v1 v2 v3 |>
            Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
        return (v, Stuple [s1; s2; s3])
     | Eseq, [e1; e2], Stuple [s1; s2] ->
        let* _, s1 = sexp genv env e1 s1 in
        let* v2, s2 = sexp genv env e2 s2 in
        return (v2, Stuple [s1; s2])
     | Erun _, [_; e], Stuple [Sinstance si; s] ->
        (* the application of a n-ary node is of the form [f(e1,..., en)] or *)
        (* [run f (e1,...,en)]. The [ei] are non strict *)
        let* v, s = sarg genv env e s in
        let* v, si = run e_loc si v in
        return (v, Stuple [Sinstance si; s])
     | Eatomic, [e], s ->
        (* if one of the input is bot (or nil), the output is bot (or nil); *)
        (* that is, [e] is considered to be strict *)
        let* v, s = sexp genv env e s in
        let* v =
          Primitives.atomic v |>
            Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
        return (v, s)
     | Etest, [e], s ->
        let* v, s = sexp genv env e s in
        let* v =
          Primitives.lift1 Primitives.test v |>
            Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
        return (v, s)
     | Eup, [e], Stuple [Szstate { zin }; s] ->
       (* [zin]: set to true when the solver detect a zero-crossing; *)
       (* [zout]: output to be followed for zero-crossing detection *)
        let* zout, s = sexp genv env e s in
        return (Value(Vbool(zin)),
                Stuple [Szstate { zin = false; zout }; s])
     | Eperiod, [_; _], Speriod ({ zin; phase; period; horizon } as p) ->
        (* Semantically: h = present zin -> last h + period init phase+period *)
        let horizon = if zin then horizon +. period else horizon in
        return
          (Value(Vbool(zin)),
           Speriod { p with horizon })
     | Ehorizon, [e], Stuple [Shorizon ({ zin; horizon } as h); s] ->
        if zin then
          let* horizon, s = sexp genv env e s in
          match horizon with
          | Vbot -> return (Vbot, Stuple [Shorizon(h); s])
          | Vnil -> return (Vnil, Stuple [Shorizon(h); s])
          | Value(v) ->
             let* horizon =
               float v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
             return
               (Value(Vbool(zin)), Stuple [Shorizon { h with horizon }; s])
        else
          return (Value(Vbool(zin)), Stuple [Shorizon(h); s])
     | _ -> error { kind = Etype; loc = e_loc }
     end
  | Econstr1 { lname; arg_list }, Stuple(s_list) ->
     let* v_list, s_list = sexp_list e_loc genv env arg_list s_list in
     (* check that all component are not nil nor bot *)
     let* v =
       constr1 lname v_list |>
         Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     return (v, Stuple(s_list))
  | Etuple(e_list), Stuple(s_list) ->
     (* pairs are considered to be strict *)
     let* v_list, s_list = sexp_list e_loc genv env e_list s_list in
     let* v =
       stuple v_list |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     return (v, Stuple(s_list))
  | Eapp(_, [e]), Stuple [Sinstance si; s] ->
     (* Here, [f (e1,..., en)] is a short-cut for [run f (e1,...,en)] *)
     let* v, s = sarg genv env e s in
     let* v, si = run e_loc si v in
     return (v, Stuple [Sinstance si; s])
  | Eapp(e, e_list), Stuple (s :: s_list) ->
     (* [f] must return a combinatorial function *)
     let* fv, s = sexp genv env e s in
     let* v_list, s_list = sarg_list e_loc genv env e_list s_list in
     (* if one element is [bot] return [bot]; if [nil] return [nil] *)
     let* v =
       match fv with
       | Vbot -> return Vbot | Vnil -> return Vnil
       | Value(fv) ->
          Combinatorial.apply e_loc fv v_list in
     return (v, Stuple (s :: s_list))
  | Elet(l_eq, e), Stuple [s_eq; s] ->
     let* env_eq, s_eq = sleq genv env l_eq s_eq in
     let env = Env.append env_eq env in
     let* v, s = sexp genv env e s in
     return (v, Stuple [s_eq; s])
  | Efun(fe), s ->
     return (Value(Vclosure { c_funexp = fe; c_genv = genv; c_env = env }), s)
  | Ematch { e; handlers }, Stuple(se :: s_list) ->
     let* ve, se = sexp genv env e se in
     let* v, s_list =
       match ve with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (Vbot, s_list)
       | Vnil -> return (Vnil, s_list)
       | Value(ve) ->
          smatch_handler_list e_loc sexp genv env ve handlers s_list in
     return (v, Stuple (se :: s_list))
  | Epresent { handlers; default_opt }, Stuple(s :: s_list) ->
     (* present z1 -> e1 | ... | zn -> en [[else|init] e]] *)
     let* v_opt, s_list =
       spresent_handler_list e_loc sscondpat Vbot Vnil
         sexp genv env handlers s_list in
     let* v, s =
       match v_opt, default_opt, s with
       | Some(v), Init(e), Stuple [Sopt(None); s] ->
          (* at the first instant, execute the initialization *)
          let* v', s = sexp genv env e s in
          return (v, Stuple [Sopt(Some(v')); s])
       | Some(v), _, _ -> return (v, s)
       | None, Else(e), s -> 
          (* no handler was selected *)
          let* v, s = sexp genv env e s in return (v, s)
       | None, Init(e), Stuple [Sopt(s_opt); s] ->
          (* no handler was selected *)
          let* v, s = sexp genv env e s in
          let* v, s =
            match s_opt with
            | None -> return (v, s) | Some(v) -> return (v, s) in
          return (v, Stuple [Sopt(Some(v)); s])
       | _ -> (* error *)
          error { kind = Estate; loc = e_loc } in
     return (v, Stuple(s :: s_list))
  | Ereset(e_body, e_res), Stuple [s_body; s_res] ->
     let* v, s_res = sexp genv env e_res s_res in 
     let* v_body, s_body =
       match v with
       | Vbot -> return (Vbot, s_body)
       | Vnil -> return (Vnil, s_body)
       | Value(v) ->
          let* v =
            bool v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
          reset iexp sexp genv env e_body s_body v in
     return (v_body, Stuple [s_body; s_res])
  | Eassert(e_body), s ->
     let* v, s = sexp genv env e_body s in
     let* r = Combinatorial.check_assertion e_loc v void in
     return (r, s)
  | Eforloop({ for_kind; for_index; for_body }),
    Stuple
      (((Sval(Value(Vint(for_size)))) as sv) ::
         s_kind :: Sarray(s_b_array) :: si_list) ->
     (* computes a local environment for variables introduced *)
     (* in the index list *)
     let* l_env, si_list =
       mapfold2 { kind = Estate; loc = e_loc }
         (sfor_index e_loc genv env) Env.empty for_index si_list in
     let* v, s_b_array =
       sfor_result e_loc genv env l_env for_body s_b_array in
     return (v, Stuple (sv :: s_kind :: Sarray(s_b_array) :: si_list))
  | _ -> error { kind = Estate; loc = e_loc }

and sfor_kind loc genv env for_kind =
  error { kind = Enot_implemented; loc }

(* evaluate a index returns a local environment *)
and sfor_index loc genv env l_env { desc; loc } s =
  match desc, s with
  | Einput(x, e, None), Stuple [se; se_opt] ->
     let* ve, se = sexp genv env e se in
     return (Env.add x ve l_env, se)
  | Einput(x, e, Some(e_by)), Stuple [se; se_opt] ->
     error { kind = Enot_implemented; loc }
  | Eindex(x, e1, e2), Stuple [se1; se2] ->
     error { kind = Enot_implemented; loc }
  | _ ->
     error { kind = Estate; loc }
             
and sfor_result loc genv env l_env for_body s_body_array =
  match for_body, s_body_array with
  | Forexp(e), se ->
     let* ve, se = sexp genv env e se in
     return (ve, se)
  | Forreturns(v_list, { for_block }), Stuple [s_list; s_b] ->
     error { kind = Enot_implemented; loc }


and sfor_block_initialize genv env { for_block } s_b =
  let* env, env_local, s_b = sblock genv env for_block s_b in
  return (env, env_local, s_b)

and sfor_initialize genv env { desc = { last_exp } } =
  sexp genv env last_exp
  
(* a function can take a tuple that is non strict *)
and sarg genv env ({ e_desc; e_loc } as e) s =
  match e_desc, s with
  | Etuple(e_list), Stuple(s_list) ->
     let* v_list, s_list = sexp_list e_loc genv env e_list s_list in
     return (Value(Vtuple(v_list)), Stuple(s_list))
  | _ ->
     sexp genv env e s

(* application of a node *)
and run loc { init; step } v =
  let* v, init = runstep loc init step v in
  return (v, { init; step })

and runstep loc s { c_funexp = { f_args; f_body }; c_genv; c_env } v =
  let matching a_list s_list v_list =
    let match_in acc vdec s v =
      let* acc, s = svardec c_genv c_env acc vdec s v in
      let* s = set_vardec acc vdec s in
      return (acc, s) in
    mapfold3 { kind = Estate; loc = loc }
      match_in Env.empty a_list s_list v_list in

  let v_list = Primitives.list_of v in
  match f_args, s with
  | [arg_list], Stuple (s_body :: s_arg_list) ->
     let* env_arg_list, s_arg_list =
       matching arg_list s_arg_list v_list in
     let env = Env.append env_arg_list c_env in
     let* r, s_body = sresult c_genv env f_body s_body in
     return (r, Stuple (s_body :: s_arg_list))
  | _ ->
     error { kind = Etype; loc = loc }
  
and sexp_list loc genv env e_list s_list =
  slist loc genv env sexp e_list s_list

and sarg_list loc genv env e_list s_list =
  slist loc genv env sarg e_list s_list

and sleq genv env { l_rec; l_eq = ({ eq_write } as l_eq); l_loc } s_eq =
  if l_rec then
    (* compute a bounded fix-point in [n] steps *)
    let bot = bot_env eq_write in
    let n = (Fix.size l_eq) + 1 in
    let* env_eq, s_eq = Fix.eq genv env seq l_eq n s_eq bot in
    (* a dynamic check of causality: all defined names in [eq] *)
    (* must be non bottom provided that all free vars. are non bottom *)
    let* _ = Fix.causal l_loc env env_eq (names eq_write) in
    return (env_eq, s_eq)     
  else
    seq genv env l_eq s_eq
    
and slets loc genv env leq_list s_list =
  mapfold2 { kind = Estate; loc }
    (fun acc leq s -> let* env, s = sleq genv env leq s in
                      return (Env.append env acc, s))
    env leq_list s_list
    
(* step function for an equation *)
and seq genv env { eq_desc; eq_write; eq_loc } s =
  match eq_desc, s with 
  | EQeq(p, e), s -> 
     let* v, s = sexp genv env e s in
     let* env_p =
       matcheq v p |>
         Opt.to_result ~none:{ kind = Epattern_matching_failure; loc = eq_loc }
     in
     (* let l = Env.bindings env_p in *)
     return (env_p, s)
  | EQder(x, e, e0_opt, p_h_list),
    Stuple (Scstate({ pos } as sc) :: s :: Sopt(x0_opt) :: s0 :: s_list) ->
     let* ({ last; default } as entry) =
       Env.find_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = eq_loc } in
     (* compute the derivative (w.r.t time) of [x] *)
     let* der, s = sexp genv env e s in
     (* computes the initial position *)
     let* cx0, x0_opt, s0 =
       match e0_opt with
       | None ->
          (* [x] should have a default value *)
          let* x0 =
            Fix.default_value last default |>
              Opt.to_result ~none:{ kind = Eno_default(x); loc = eq_loc } in
          return (x0, x0_opt, s0)
       | Some(e0) ->
          match x0_opt with
          | None -> (* first instant *)
             let* x0, s0 = sexp genv env e0 s0 in
             return (x0, Some(x0), s0)
          | Some(x0) -> return (x0, x0_opt, s0) in
     let* cx_opt, s_h_list =
       spresent_handler_list
         eq_loc sscondpat Vbot Vnil sexp genv env p_h_list s_list in
     let cur =
       match cx_opt with
       | None ->
          (* no event is present; return the value computed by the solver *)
          pos
       | Some(cx) ->
          (* otherwise the value returned by the handler *)
          cx in
     return (Env.singleton x { entry with cur },
             Stuple (Scstate({ sc with der }) :: Sopt(x0_opt) :: s0 :: s_list))
  | EQinit(x, e), Stuple [Sopt(None); se] ->
     (* first step *)
     let* v, se = sexp genv env e se in
     let* ({ cur } as entry) =
       Env.find_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = eq_loc } in
     return (Env.singleton x { entry with last = Some(v) },
             Stuple [Sopt(Some(cur)); se])
  | EQinit(x, e), Stuple [Sopt(Some(v)); se] ->
     (* remaining steps *)                     
     let* ({ cur } as entry) =
       Env.find_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = eq_loc } in
     return (Env.singleton x { entry with last = Some(v) },
             Stuple [Sopt(Some(cur)); se])
  | EQif(e, eq1, eq2), Stuple [se; s_eq1; s_eq2] ->
      let* v, se = sexp genv env e se in
      let* env_eq, s =
        match v with
        (* if the condition is bot/nil then all variables have value bot/nil *)
        | Vbot -> return (bot_env eq_write, Stuple [se; s_eq1; s_eq2])
        | Vnil -> return (nil_env eq_write, Stuple [se; s_eq1; s_eq2])
        | Value(b) ->
           let* v =
             bool b |> Opt.to_result ~none:{ kind = Etype; loc = e.e_loc } in
           if v then
             let* env1, s_eq1 = seq genv env eq1 s_eq1 in
             (* complete the output environment with default *)
             (* or last values from all variables defined in [eq_write] but *)
             (* not in [env1] *)
             let* env1 = Fix.by eq_loc env env1 (names eq_write) in
             return (env1, Stuple [se; s_eq1; s_eq2]) 
           else
             let* env2, s_eq2 = seq genv env eq2 s_eq2 in
             (* symetric completion *)
             let* env2 =
               Fix.by eq_loc env env2 (names eq_write) in
             return (env2, Stuple [se; s_eq1; s_eq2]) in
      return (env_eq, s)
  | EQand(eq_list), Stuple(s_list) ->
     let seq genv env acc eq s =
       let* env_eq, s = seq genv env eq s in
       let* acc = Combinatorial.merge eq_loc env_eq acc in
       return (acc, s) in
     let* env_eq, s_list =
       mapfold2 { kind = Estate; loc = eq_loc }
         (seq genv env) Env.empty eq_list s_list in
     return (env_eq, Stuple(s_list))
  | EQreset(eq, e), Stuple [s_eq; se] -> 
     let* v, se = sexp genv env e se in 
     let* env_eq, s_eq =
       match v with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write, Stuple [s_eq; se])
       | Vnil -> return (nil_env eq_write, Stuple [s_eq; se])
       | Value(v) ->
          let* v =
            bool v |> Opt.to_result ~none:{ kind = Etype; loc = e.e_loc } in
          reset ieq seq genv env eq s_eq v in    
     return (env_eq, Stuple [s_eq; se])
  | EQlocal(b_eq), s_eq ->
     let* _, env_local, s_eq = sblock genv env b_eq s_eq in
     return (env_local, s_eq)
  | EQautomaton { is_weak; handlers; state_opt },
    Stuple (ps :: Sval(pr) :: si :: s_list) ->
     (* [ps] = state where to go; *)
     (* [pr] = whether the state must be reset or not *)
     (* [si] state for [state_opt]; [s_list] state for [handlers] *)
     let* ps, si =
       match ps, state_opt with
       | Sval(ps), _ ->
          return (ps, si)
       | Sopt(None), Some(state) ->
          (* an initial state is given; but has never been evaluated *)
          let* v, si = sstate genv env state si in
          return (v, si)
       | _ -> 
          error { kind = Estate; loc = eq_loc } in
     let* env, ns, nr, s_list =
       match ps, pr with
       | (Vbot, _) | (_, Vbot) ->
          return (bot_env eq_write, ps, pr, s_list)
       | (Vnil, _) | (_, Vnil) ->
          return (nil_env eq_write, ps, pr, s_list)
       | Value(ps), Value(pr) ->
          let* pr =
            bool pr |> Opt.to_result ~none:{ kind = Etype; loc = eq_loc } in
          sautomaton_handler_list eq_loc
            is_weak genv env eq_write handlers ps pr s_list in
     return (env, Stuple (Sval(ns) :: Sval(nr) :: si :: s_list))
  | EQmatch { e; handlers }, Stuple (se :: s_list) ->
     let* ve, se = sexp genv env e se in
     let* env, s_list =
       match ve with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write, s_list)
       | Vnil -> return (nil_env eq_write, s_list)
       | Value(ve) ->
          let* env_handler, s_list =
            smatch_handler_list eq_loc seq genv env ve handlers s_list in
          (* complete missing entries in the environment *)
          let* env_handler = Fix.by eq_loc env env_handler (names eq_write) in
          return (env_handler, s_list) in
     return (env, Stuple (se :: s_list))
  | EQpresent { handlers; default_opt }, Stuple(s :: s_list) ->
     (* present z1 -> eq1 | ... | zn -> eqn [else eq] *)
     let* env_handler_opt, s_list =
       spresent_handler_list eq_loc
         sscondpat (bot_env eq_write) (nil_env eq_write)
         seq genv env handlers s_list in
     let* env_handler, s =
       match env_handler_opt, default_opt, s with
       | None, Else(eq), s ->
          (* [present z1 -> eq1 | ... else eq] *)
          (* no branch was selected *)
          let* env_handler, s = seq genv env eq s in return (env_handler, s)
       | None, NoDefault, s -> return (Env.empty, s)
       (* [present z1 -> eq1 | ...] *)
       | Some(env_handler), _, _ -> return (env_handler, s)
       | _, Init _, s ->
          (* this case should not arrive; no [init ...] with a present between *)
          (* equations. *)
          error { kind = Eunexpected_failure; loc = eq_loc } in
     (* complete missing entries in the environment *)
     let* env_handler = Fix.by eq_loc env env_handler (names eq_write) in
     return (env_handler, Stuple (s :: s_list))
  | EQempty, s -> return (Env.empty, s)
  | EQassert(e), s ->
     let* ve, s = sexp genv env e s in
     let* r = Combinatorial.check_assertion eq_loc ve Env.empty in
     return (r, s)
  | EQforloop({ for_kind; for_index; for_body }),
    Stuple (Sval(Value(Vint(for_size))) :: s_kind :: s_b :: si_list) ->
     error { kind = Estate; loc = eq_loc }
  | _ -> error { kind = Estate; loc = eq_loc }

(* Combinatorialuation of the result of a function *)            
and sresult genv env { r_desc; r_loc } s =
  match r_desc with
  | Exp(e) -> sexp genv env e s
  | Returns(b) ->
     (* let l1 = Env.bindings env in *)
     let* env, _, s = sblock genv env b s in
     (* let l2 = Env.bindings env in *)
     let* v = matching_arg_out env b in
     return (v, s)

(* Return a value from a block. In case of a tuple, this tuple is not strict *)
and matching_arg_out env { b_vars; b_loc } =
  let* v_list =
    map
      (fun { var_name } ->
        find_value_opt var_name env |>
          Opt.to_result
            ~none:{ kind = Eunbound_ident(var_name); loc = b_loc }) b_vars in
  match v_list with
  | [] -> return void
  | [v] -> return v
  | _ -> (* return a non strict tuple *)
     return (Value(Vtuple(v_list)))

(* block [local x1 [init e1 | default e1 | ],..., xn [...] do eq done *)
and sblock genv env { b_vars; b_body = ({ eq_write } as eq); b_loc } s_b =
  match s_b with
  | Stuple (s_eq :: s_list) ->
     let* env_v, s_list =
       mapfold3 { kind = Estate; loc = b_loc }
         (svardec genv env) Env.empty b_vars s_list (bot_list b_vars) in
     let bot = Fix.complete env env_v (names eq_write) in
     let n = (Fix.size eq) + 1 in
     let* env_eq, s_eq = Fix.eq genv env seq eq n s_eq bot in
     (* a dynamic check of causality for [x1,...,xn] *)
     let _ = Fix.causal b_loc env env_eq (names_env env_v) in
     (* store the next last value *)
     let* s_list = map2 { kind = Estate; loc = b_loc }
                     (set_vardec env_eq) b_vars s_list in
     (* remove all local variables from [env_eq] *)
     let env = Env.append env_eq env in
     let env_eq = remove env_v env_eq in
     return (env, env_eq, Stuple (s_eq :: s_list))
  | _ ->
     error { kind = Estate; loc = b_loc }

and sblock_with_reset genv env b_eq s_eq r =
  let* s_eq =
    if r then
      (* recompute the initial state *)
      iblock genv env b_eq
    else
      (* keep the current one *)
      return s_eq in
  sblock genv env b_eq s_eq
  
and svardec genv env acc
  { var_name; var_init; var_default; var_loc; var_is_last } s v =
  match s with
  | Stuple [s_init;s_default] ->
     let* default, s_default =
       match var_default, s_default with
       | None, se -> return (None, se)
       | Some(e), se ->
          let* ve, se = sexp genv env e se in
          return (Some(ve), se) in
     let* last, s_init =
       match var_init, s_init with
       | None, se ->
          if var_is_last then
            match se with
            | Sval(v) -> return (Some(v), se)
            | _ -> error { kind = Estate; loc = var_loc }
          else return (None, se)
       | Some(e), Stuple [Sopt(None); se] ->
          (* first instant *)
          let* ve, se = sexp genv env e se in
          return (Some(ve), Stuple [Sopt(None); se])
       | _, Stuple [Sopt(Some(v)); _] ->
          (* return the stored value *)
          return (Some(v), s_init)
       | _ -> error { kind = Estate; loc = var_loc } in
     let entry = { cur = v; last = last; default = default } in
     return (Env.add var_name entry acc, Stuple [s_init; s_default])
  | _ ->
     error { kind = Estate; loc = var_loc }
    
(* store the next value for [last x] in the state of [vardec] declarations *)
(* the state is organised in [s_init; s_default] *)
and set_vardec env_eq { var_name; var_loc } s =
  let* v =
    find_value_opt var_name env_eq |>
      Opt.to_result ~none:{ kind = Eundefined_ident(var_name); loc = var_loc } in
  match s with
  | Stuple [Sempty; _] -> return s
  | Stuple [Stuple [Sopt _; s_init]; s_default] ->
     (* store the current value of [var_name] into the state *)
     return (Stuple [Stuple [Sopt(Some(v)); s_init]; s_default])
  | Stuple [_; s_default] ->
     (* store the current value of [var_name] into the state *)
     return (Stuple [Sval(v); s_default])
  | _ ->
     error { kind = Estate; loc = var_loc }

(* remove entries [x, entry] from [env_eq] for *)
(* every variable [x] defined by [env_v] *)
and remove env_v env_eq =
  Env.fold (fun x _ acc -> Env.remove x acc) env_v env_eq

and sautomaton_handler_list loc is_weak genv env eq_write a_h_list ps pr s_list =
  (* automaton with weak transitions *)
  let rec body_and_transition_list a_h_list s_list =
    match a_h_list, s_list with
    | { s_state; s_let; s_body; s_trans; s_loc } :: a_h_list,
      (Stuple [Stuple(ss_let); ss_body;
               Stuple(ss_trans)] as s) :: s_list ->
       let r = Match.matchstate ps s_state in
       let* env_handler, ns, nr, s_list =
         match r with
         | None ->
            (* this is not the good state; try an other one *)
            let* env_handler, ns, nr, s_list =
              body_and_transition_list a_h_list s_list in
            return (env_handler, ns, nr, s :: s_list)            
         | Some(env_state) ->
            let env_state = liftv env_state in
            let env = Env.append env_state env in
            (* execute the local lets *)
            let* env, ss_let = slets s_loc genv env s_let ss_let in
            (* execute the body *)
            let* env, env_body, ss_body =
              sblock_with_reset genv env s_body ss_body pr in
            (* execute the transitions *)
            let* env_trans, (ns, nr), ss_trans =
              sescape_list s_loc genv env s_trans ss_trans ps pr in
            return
              (env_body, ns, nr,
               Stuple [Stuple(ss_let); ss_body;
                       Stuple(ss_trans)] :: s_list) in
       (* complete missing entries in the environment *) 
       let* env_handler = Fix.by s_loc env env_handler (names eq_write) in
       return (env_handler, ns, nr, s_list)
    | _ ->
       error { kind = Estate; loc = loc } in 
  
  (* automaton with strong transitions *)
  (* 1/ choose the active state by testing unless transitions of the *)
  (* current state *)
  let rec transition_list a_h_list s_list =
    match a_h_list, s_list with
    | { s_state; s_trans; s_loc } :: a_h_list,
      (Stuple [ss_var; ss_body; Stuple(ss_trans)] as s) :: s_list ->
       let r = Match.matchstate ps s_state in
       begin match r with
       | None ->
          (* this is not the good state; try an other one *)
          let* env_trans, ns, nr, s_list = transition_list a_h_list s_list in
          return (env_trans, ns, nr, s :: s_list)            
       | Some(env_state) ->
          let env_state = liftv env_state in
          let env = Env.append env_state env in
          (* execute the transitions *)
          let* env_trans, (ns, nr), ss_trans =
            sescape_list s_loc genv env s_trans ss_trans ps pr in
          return
            (env_trans, ns, nr,
             Stuple [ss_var; ss_body; Stuple(ss_trans)] :: s_list)
       end
    | _ -> error { kind = Estate; loc = loc } in
  (* 2/ execute the body of the target state *)
  let rec body_list a_h_list ps pr s_list =
    match a_h_list, s_list with
    | { s_state; s_let; s_body; s_loc } :: a_h_list,
      (Stuple [Stuple(ss_let); ss_body; ss_trans] as s) :: s_list ->
       let r = Match.matchstate ps s_state in
       begin match r with
       | None ->
          (* this is not the good state; try an other one *)
          let* env_body, s_list = body_list a_h_list ps pr s_list in
          return (env_body, s :: s_list)            
       | Some(env_state) ->
          let env_state = liftv env_state in
          let env = Env.append env_state env in
          (* execute the local lets *)
          let* env, ss_let = slets s_loc genv env s_let ss_let in
          (* execute the body *)
          let* _, env_body, ss_body =
            sblock_with_reset genv env s_body ss_body pr in
          return
            (env_body, Stuple [Stuple(ss_let); ss_body;
                               ss_trans] :: s_list)
       end
   | _ -> error { kind = Estate; loc = loc } in
  if is_weak then
    body_and_transition_list a_h_list s_list
  else
    (* chose the active state *)
    let* env_trans, ns, nr, s_list = transition_list a_h_list s_list in
    (* execute the current state *)
    match ns, nr with
    | (Vbot, _) | (_, Vbot) ->
       return (bot_env eq_write, ns, nr, s_list)
    | (Vnil, _) | (_, Vnil) ->
       return (bot_env eq_write, ns, nr, s_list)
    | Value(vns), Value(vnr) ->
       let* vnr =
         bool vnr |>
           Opt.to_result ~none:{ kind = Etype; loc = loc } in
       let* env_body, s_list = body_list a_h_list vns vnr s_list in
       let env_handler = Env.append env_trans env_body in
       (* complete missing entries in the environment *)
       let* env_handler = Fix.by loc env env_handler (names eq_write) in
       return (env_handler, ns, nr, s_list)

(* [Given a transition t, a name ps of a state in the automaton, a value pr *)
(* for the reset condition, *)
(* [escape_list genv env { e_cond; e_vars; e_body; e_next_state } ps pr] *)
(* returns an environment, a new state name, a new reset condition and *)
(* a new state *)
and sescape_list loc genv env escape_list s_list ps pr =
  match escape_list, s_list with
  | [], [] -> return (Env.empty, (Value ps, Value (Vbool false)), [])
  | { e_cond; e_reset; e_let; e_body; e_next_state; e_loc } :: escape_list,
    Stuple [s_cond; Stuple(ss_let); s_body; s_next_state] :: s_list ->
     (* if [pr=true] then the transition is reset *)
     let* (v, env_cond), s_cond =
       reset iscondpat sscondpat genv env e_cond s_cond pr in
     let env = Env.append env_cond env in
     let* env_body, (ns, nr), s =
       match v with
       (* if [v = bot/nil] the state and reset bit are also bot/nil *)
       | Vbot ->
          return (bot_env e_body.b_write,
                  (Vbot, Vbot), Stuple [s_cond; Stuple(ss_let);
                                        s_body; s_next_state] :: s_list)
       | Vnil ->
          return (nil_env e_body.b_write, 
                  (Vnil, Vnil), Stuple [s_cond; Stuple(ss_let);
                                        s_body; s_next_state] :: s_list)
       | Value(v) ->
          (* revoir le traitement. L'etat des conditions *)
          (* change mais les equations ne sont evaluees que lorsque *)
          (* la condition est vraie *)
          (* le code ci-dessous ne le fait pas. *)
          let* v =
            bool v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
          (* execute the local lets *)
          let* env, ss_let = slets e_loc genv env e_let ss_let in
          let* env, env_body, s_body =
            sblock_with_reset genv env e_body s_body pr in
          let* ns, s_next_state = sstate genv env e_next_state s_next_state in
          let* env_others, (s, r), s_list =
            sescape_list loc genv env escape_list s_list ps pr in
          let ns, nr = 
            if v then (ns, Value(Vbool(e_reset))) else (s, r) in
          return (env_body, (ns, nr),
                  Stuple [s_cond; Stuple(ss_let);
                          s_body; s_next_state] :: s_list) in
     return (env_body, (ns, nr), s)
  | _ ->
     error { kind = Estate; loc = loc }

and sscondpat (genv : pvalue genv) (env : value ientry Env.t ) { desc; loc } s =
  match desc, s with
  | Econdand(sc1, sc2), Stuple [s1; s2] ->  
     let* (v1, env_sc1), s1 = sscondpat genv env sc1 s1 in
     let* (v2, env_sc2), s2 = sscondpat genv env sc2 s2 in
     let* env_sc = Combinatorial.merge loc env_sc1 env_sc2 in
     let s = Stuple [s1; s2] in 
     (match v1, v2 with
      | (Vbot, _) | (_, Vbot) -> return ((Vbot, Env.empty), s)
      | (Vnil, _) | (_, Vnil) -> return ((Vnil, Env.empty), s)
      | Value(v1), Value(v2) ->
         let* v1 =
           bool v1 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         let* v2 =
           bool v2 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         (* v1 && v2 *) 
         return ((Value(Vbool(v1 && v2)), env_sc), s))
  | Econdor(sc1, sc2), Stuple [s1; s2] ->
     let* (v1, env_sc1), s1 = sscondpat genv env sc1 s1 in
     let* (v2, env_sc2), s2 = sscondpat genv env sc2 s2 in
     let* env_sc = Combinatorial.merge loc env_sc1 env_sc2 in
     (match v1, v2 with
      | (Vbot, _) | (_, Vbot) -> return ((Vbot, Env.empty), s)
      | (Vnil, _) | (_, Vnil) -> return ((Vnil, Env.empty), s)
      | Value(v1), Value(v2) ->
         let* v1 =
           bool v1 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         let* v2 =
           bool v2 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         (* v1 or v2 *) 
         return ((Value(Vbool(v1 || v2)), env_sc), s))
  | Econdexp(e_cond), s ->
     let* v, s = sexp genv env e_cond s in
     return ((v, Env.empty), s)
  | Econdpat(e, p), s ->
     let* ve, s = sexp genv env e s in
     let* ve, env_p =
       Match.matchsig ve p |>
         Opt.to_result ~none:{ kind = Epattern_matching_failure; loc = loc } in
     return ((ve, env_p), s)
  | Econdon(sc, e), Stuple [s_sc; s] ->
     let* (v, env_sc), s_sc = sscondpat genv env sc s_sc in
     let* ve, s = sexp genv env e s in
     let s = Stuple [s_sc; s] in
     (match v, ve with
      | (Vbot, _) | (_, Vbot) -> return ((Vbot, env_sc), s)
      | (Vnil, _) | (_, Vnil) -> return ((Vnil, env_sc), s)
      | Value(v), Value(ve) ->
         let* v =
           bool v |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         let* ve =
           bool ve |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         (* v on ve *) 
         return ((Value(Vbool(v && ve)), env_sc), s))
  | _ -> error { kind = Estate; loc = loc }
       
and sstate genv env { desc; loc } s =
  match desc, s with
  | Estate0(f), Sempty -> return (Value(Vstate0(f)), Sempty)
  | Estate1(f, e_list), Stuple s_list ->
     let* v_s_list =
       map2 { kind = Estate; loc = loc } (sexp genv env) e_list s_list in
     let v_list, s_list = List.split v_s_list in
     let* c =
       Primitives.state1 f v_list
       |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
     return (c, Stuple(s_list))
  | Estateif(e, s1, s2), Stuple [se; se1; se2] ->
     let* v, se = sexp genv env e se in
     let* s1, se1 = sstate genv env s1 se1 in
     let* s2, se2 = sstate genv env s2 se2 in
     let* v =
       Primitives.ifthenelse v s1 s2 |>
         Opt.to_result ~none:{ kind = Etype; loc = loc } in
     return (v, Stuple [se; se1; se2])
  | _ -> error { kind = Estate; loc = loc }
       
   
(* check that a value is neither bot nor nil *)
let no_bot_no_nil loc v =
  match v with
  | Vbot -> error { kind = Ebot; loc = loc }
  | Vnil -> error { kind = Enil; loc = loc }
  | Value(v) -> return v

let implementation genv { desc; loc } =
  match desc with
  | Eopen(name) ->
     (* add [name] in the list of known modules *)
     return (Genv.open_module genv name)
  | Eletdecl(f, e) ->
     (* add the entry [f, v] in the current global environment *)
     let* v = Combinatorial.exp genv Env.empty e in
     let* v = no_bot_no_nil loc v in
     (* debug info (a bit of imperative code here!) *)
     if !print_values then Output.letdecl Format.std_formatter f v;
     return (add f v genv)
  | Etypedecl _ ->
     return genv
     
let catch e = 
  match e with
  | Ok(r) -> r
  | Error { kind; loc } ->  Error.message loc kind; raise Smisc.Error

(* The main function *)
let program genv i_list = catch (fold implementation genv i_list)
                            
(* run a unit process for [n_steps] steps *)
let run_n n_steps init step v_list =
  let rec apply_rec s i =
    if i = n_steps then s
    else
      let r = step s v_list in
      match r with
      | Error { kind; loc } ->
         Error.message loc kind;
         Format.eprintf "@[Zrun: %d iterations out of %d.@.@]" i n_steps;
         raise Smisc.Error
      | Ok(s) ->
         apply_rec s (i+1) in
  let _ = apply_rec init 0 in ()
                            
let run_fun loc output n_steps fv v_list =
  let step s v_list =
    let* v = Combinatorial.apply loc fv v_list in
    output v; return s in
  run_n n_steps Sempty step v_list

let run_node loc output n_steps { init; step } v  =
  let step s v =
    let* v, s = runstep loc s step v in
    output v; return s in
  run_n n_steps init step v
