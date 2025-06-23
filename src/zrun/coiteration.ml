(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2025 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* This file defines a functional (executable) semantics for a
 *- synchronous language like Lustre, Scade, Lucid Synchrone and Zelus.
 *- It is based on a companion file and working notes on the co-iterative
 *- semantics presented at the SYNCHRON workshop, December 2019,
 *- the class on "Advanced Functional Programming" given at Bamberg
 *- Univ. in June-July 2019 and slides for Master MPRI - M2, Fall 2019, 2020, 2021
 *- The original version of this code is taken from the GitHub ZRun repo:
 *- https://github.com/marcpouzet/zrun
 *- ZRun was programmed right after the COVID confinment, in May-June 2020
 *- This second version includes some of the Zelus constructs:
 *- ODEs and zero-crossing; higher order functions;
 *- the implem. was done in 2021 and updated since then;
 *- first update during summer 2022 with array constructs inspired by the
 *- loop construct from SISAL language expressed in a purely-functional form;
 *- a first version of loop iteration (the "foreach" was named "forall" and was
 *- implemented in Zelus V2 in 2017).
 *- Two style of loop iterations are provided:
 *- 1/ The "foreach" loop iteration runs several instances of a stream
 *- function (say f); in operational terms, every application has it own state; it
 *- corresponds to the classical "map" operation:
 *- the input is an array of streams and the output is an array of streams.
 *- 2/ The forward loop is an "hyper-serial" loop iteration: the array of input
 *- stream is interpreted as a faster stream passed to [f] and whose result
 *- is converted back into an array of streams. In this form, it is possible
 *- to reset [f] for every new array coming in or not. And it is possible to
 *- return the array of successive computation or only the very last one.
 *- This construction is the data-flow version of the "clock domains" construct
 *- of ReactiveML (PPDP'13 and SCP'15; by L. Mandel, C. Pasteur and M. Pouzet)
 *- and the work on temporal refinement studied by Caspi and Mikac. It
 *- performs several successive synchronous reactions but a single one is
 *- observable. In term of generated code, it generated a for loop.
 *- In this work, the size of arrays and maximum number of iterations must 
 *- be known statically.
 *-
 *- If you find the work on ZRun work useful for your research, please cite
 *- the [EMSOFT'2023] paper. Do not hesitate to send us a mail: 
 *- [Marc.Pouzet@ens.fr]
 *)

open Misc
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
open Debug

(* [let+ x = e in e'] returns [bot] if [e] returns bot; *)
(* nil if e returns nil; [e'] otherwise *)
let (let+) v f =
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) -> f v

let (and+) v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(v1, v2)

(* check that a value is neither bot nor nil *)
let no_bot_no_nil loc v =
  match v with
  | Vbot -> error { kind = Ebot; loc = loc }
  | Vnil -> error { kind = Enil; loc = loc }
  | Value(v) -> return v
    
let no_bot_no_nil_env loc env =
  let seq_env = Env.to_seq env in
  seqfold 
    (fun acc (f, { cur }) -> 
      match cur with
      | None -> return acc
      | Some(v) -> let* v = no_bot_no_nil loc v in return (Env.add f v acc))
    Env.empty seq_env

(* merge two environments provided they do not overlap *)
let merge loc env1 env2 =
  let merge init x v1 v2 = match v1, v2 with
    | Some _, Some _ -> error { kind = Emerge_env { init; id = x }; loc }
    | Some _, _ -> return v1
    | None, _ -> return v2 in
  let env2_in_1, env2 = Env.partition (fun x _ -> Env.mem x env1) env2 in
  if Env.is_empty env2_in_1 then
    return (Env.append env1 env2)
  else 
    let s1 = Env.to_seq env1 in
    seqfold
      (fun acc (x, ({ cur = cur1; last = last1; reinit = r1 } as entry)) ->
        if Env.mem x env2_in_1 then
          let { cur = cur2; last = last2; reinit = r2 } = 
            Env.find x env2_in_1 in
          let* cur = merge false x cur1 cur2 in
          let* last = merge true x last1 last2 in
          return (Env.add x { empty with cur; last; reinit = r1 || r2 } acc)
        else return (Env.add x entry acc))
      env2 s1

(* check assertion *)
let check_assertion loc ve ret =
  (* when ve is not bot/nil it must be true *)
  match ve with
  | Vnil | Vbot -> return ret
  | Value(v) ->
     let* v = is_bool v |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
     (* stop when [no_assert = true] *)
     if !no_assert || v then return ret
     else error { kind = Eassert_failure; loc = loc }

let check_equality loc v0 v1 =
  match v0, v1 with
  | (Vbot, Vbot) | (Vnil, Vnil) -> return true
  | (Vbot, Vnil) | (Vnil, Vbot) -> return false
  | Value(v0), Value(v1) ->
     let* v =
       Primitives.compare_pvalue v0 v1 |> 
         Opt.to_result ~none: { kind = Etype; loc } in
     return (v = 0)
  | (Value _, Vnil) | (Vnil, Value _) -> error { kind = Enil; loc }
  | (Value _, Vbot) | (Vbot, Value _) -> error { kind = Ebot; loc }

(* check that a value is an integer *)
let is_int loc v =
  let* v = Primitives.pvalue v |>
             Opt.to_result ~none: { kind = Etype; loc } in
  (* and an integer value *)
  Primitives.is_int v |> Opt.to_result ~none: { kind = Etype; loc}

(* [reset init step genv env body s r] resets [step genv env body] *)
(* when [r] is true *)
let reset init step genv env body s r =
  let*s = if r then init genv env body else return s in
  step genv env body s

(* Pattern matching *)
let imatch_handler is_fun ibody genv env { m_body } =
  ibody is_fun genv env m_body

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

(* the argument [ve] is static and [s] is the state of the selected branch *)
let static_match_handler_list loc sbody genv env ve m_h_list s =
  let rec smatch_rec m_h_list =
    match m_h_list with
    | [] -> error { kind = Epattern_matching_failure; loc = loc }
    | { m_pat; m_body } :: m_h_list ->
       let r = Match.pmatch ve m_pat in
       let* r, s =
         match r with
         | None ->
            (* this is not the good handler; try an other one *)
            smatch_rec m_h_list
         | Some(env_pat) ->
            let env_pat = liftv env_pat in
            let env = Env.append env_pat env in
            sbody genv env m_body s in
       return (r, s) in
  smatch_rec m_h_list

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

(* an other iterator which stops when the accumulator is bot or nil *)
let mapfold2v k_error f acc x_list s_list =
  let rec maprec acc x_list s_list =
    match x_list, s_list with
    | [], [] -> return (Value acc, [])
    | ([], _) | (_, []) -> error k_error
    | x :: x_list, s :: s_list ->
       let* acc, s = f acc x s in
       match acc with
       | Vbot -> return (Vbot, s :: s_list)
       | Vnil -> return (Vnil, s :: s_list)
       | Value(v) ->
          let* acc, s_list = maprec v x_list s_list in
          return (acc, s :: s_list) in
  maprec acc x_list s_list

(* Return a value from a block. In case of a tuple, this tuple is not strict *)
let matching_out env { b_vars; b_loc } =
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

(* Return a value for a for loop *)
(* [env_list] is the list of environments, each produced by an iteration *)
(* [acc_env] is the final environment for the accumulated variables *)
(* [x init v ] : returns the accumulated value of [x] *)
(* [[|x init v|] : returns an array of the accumulated values of [x] *)
(* [x] : returns an array of the accumulated values of [x]; the value of *)
(* [last x] is initialized with nil *)
(* [|x|] : returns an array such that [x.(i) = env_list.(i).(x)] *)
(* [non_filled] is the number of iterations not done in case of a forward loop *)
let for_matching_out missing env_list acc_env returns =
  let* v_list =
    map
      (fun { desc = { for_array;
                      for_vardec = { var_name; var_init; var_default } };
             loc } ->
        match for_array with
        | 0 ->
          (* accumulation. look for acc_env(last var_name) *)
          find_last_opt var_name acc_env |>
          Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc }
        | 1 ->
          Forloop.array_of missing loc
            (var_name, var_init, var_default) acc_env env_list
        | _ -> (* this case is not treated for the moment *)
          (* loop iteration only crosses a single dimension *)
          error 
            { kind = Earray_dimension_in_iteration 
                  { expected_dimension = 1; actual_dimension = for_array };
              loc }) returns in
  match v_list with
  | [] -> return void
  | [v] -> return v
  | _ -> (* return a non strict tuple *)
     return (Value(Vtuple(v_list)))

(* given a list of environments [env_list = [env.(0);...;env.(n-1)]], that is *)
(* one per loop iteration) and an accumulated environment [acc_env] *)
(* return the environment [env'] computed by a for loop *)
(* [env'(x) = acc_env(last x)] if x in Dom(acc_env) and *)
(* [env'(x).(i) = env_list.(i).(x) otherwise *)
let for_env_out missing env_list acc_env loc for_out =
  fold
    (fun acc { desc = { for_name; for_init; for_default; for_out_name }; loc } ->
      match for_out_name with
       | None ->
         (* accumulation. look for acc_env(last var_name) *)
         let* v =
           Find.find_last_opt for_name acc_env |>
             Opt.to_result ~none:{ kind = Eunbound_last_ident(for_name); loc } in
         return (Env.add for_name { empty with cur = Some v } acc)
      | Some(x) ->
         let* v = Forloop.array_of missing loc
                    (for_name, for_init, for_default) acc_env env_list in
         return (Env.add x { empty with cur = Some v } acc))
    Env.empty for_out

(* value of an immediate constant *)
let immediate v =
  match v with
  | Eint(v) -> Vint(v)
  | Ebool(b) -> Vbool(b)
  | Evoid -> Vvoid
  | Efloat(f) -> Vfloat(f)
  | Echar(c) -> Vchar(c)
  | Estring(s) -> Vstring(s)

(* sizes *)
let rec size env { desc; loc } =
  match desc with
  | Size_int(i) -> return i
  | Size_frac { num; denom} ->
      let* v = size env num in
      return (v / denom)
  | Size_var(x) ->
      let* v =
       find_value_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc } in
      let* v = is_int loc v in
      return v
  | Size_op(op, s1, s2) ->
     let* v1 = size env s1 in
     let* v2 = size env s2 in
     match op with
     | Size_plus -> return (v1 + v2)
     | Size_minus -> return (v1 - v2)
     | Size_mult -> return (v1 * v2)

(* mutually recursive definitions must either define *)
(* functions parameterized by a size or stream values *)
let sizefun_defs_or_values genv env l_eq =
  let rec split (acc, one_value) { eq_desc; eq_loc } =
    match eq_desc with
    | EQsizefun { sf_id; sf_id_list; sf_e } ->
       if one_value then
         error { kind = Esizefun_def_recursive; loc = eq_loc }
       else return (Env.add sf_id { s_params = sf_id_list; 
                                    s_body = sf_e; s_genv = genv; 
                                    s_env = env } acc,
                 one_value)
    | EQand { eq_list } ->
       fold split (acc, one_value) eq_list
    | EQempty -> 
       return (acc, one_value)
    | _ -> 
      if Env.is_empty acc then return (acc, true)
      else error { kind = Esizefun_def_recursive; loc = eq_loc } in
  let* acc, one_value = split (Env.empty, false) l_eq in
  if one_value then
    return (Either.Left(l_eq))
  else
    return (Either.Right(acc))

let sizefun_defs genv env { l_eq; l_loc } =
  let* v = sizefun_defs_or_values genv env l_eq in
  match v with 
  | Right(defs) -> return defs 
  | Left _ -> error { kind = Esizefun_def_recursive; loc = l_loc }

(* Present handler *)
(* In the code below, [is_fun] is a boolean flag. When true, the expression *)
(* is expected to be combinational. If it is not, an error is raised *)
let ipresent_handler is_fun iscondpat ibody genv env { p_cond; p_body } =
  let* sc = iscondpat is_fun genv env p_cond in
  let* sb = ibody is_fun genv env p_body in
  return (Slist [sc; sb])

let idefault_opt is_fun ibody genv env default_opt =
  match default_opt with
  | Init(b) -> ibody is_fun genv env b
  | Else(b) -> ibody is_fun genv env b
  | NoDefault -> return Sempty

let spresent_handler_list loc sscondpat bot nil sbody genv env p_h_list s_list =
  let rec spresent_rec p_h_list s_list =
    match p_h_list, s_list with
    | [], [] ->
       return (Opt.none, []) (* no condition is true *)
    | { p_cond; p_body; p_loc } :: p_h_list, Slist [s_cond; s_body] :: s_list ->
       let* (r, env_pat), s_cond = sscondpat genv env p_cond s_cond in
       let* r, s =
         match r with
         | Vbot ->
            return (Opt.return bot, Slist [s_cond; s_body] :: s_list)
         | Vnil ->
            return (Opt.return nil, Slist [s_cond; s_body] :: s_list)
         | Value(v) ->
            let* v =
              Opt.to_result ~none:{ kind = Etype; loc = p_loc } (is_bool v) in
            if v then
              (* this is the good handler *)
              let env = Env.append env_pat env in
              let* r, s_body = sbody genv env p_body s_body in
              return (Opt.return r, Slist [s_cond; s_body] :: s_list)
            else
              let* r, s_list = spresent_rec p_h_list s_list in
              return (r, Slist [s_cond; s_body] :: s_list) in
       return (r, s)
    | _ -> error { kind = Estate; loc = loc } in
  spresent_rec p_h_list s_list

(* [sem genv env e = CoF f s] such that [iexp is_fun genv env e = s] *)
(* when [is_fun = true], [e] is expected to be combinational *)
let rec iexp is_fun genv env { e_desc; e_loc  } =
(* and [sexp genv env e = f] *)
  match e_desc with
  | Econst _ | Econstr0 _ | Evar _ | Eglobal _ | Elast _ ->
     return Sempty
  | Econstr1 { arg_list } ->
     let* s_list = map (iexp is_fun genv env) arg_list in
     return (Slist(s_list))
  | Eop(op, e_list) ->
     begin match op, e_list with
     | Efby, [{ e_desc = Econst(v) }; e] ->
        (* synchronous register initialized with a static value *)
        if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
        else let* s = iexp is_fun genv env e  in
          return (Slist [Sval(Value (immediate v)); s])
     | Efby, [e1; e2] ->
        if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
        else let* s1 = iexp is_fun genv env e1 in
          let* s2 = iexp is_fun genv env e2 in
          return (Slist [Sopt(None); s1; s2])
     | Eunarypre, [e] ->
        (* un-initialized synchronous register *)
        if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
        else let* s = iexp is_fun genv env e in
          return (Slist [Sval(Vnil); s])
     | Eminusgreater, [e1; e2] ->
        if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
        else let* s1 = iexp is_fun genv env e1 in
          let* s2 = iexp is_fun genv env e2 in
          return (Slist [Sval(Value(Vbool(true))); s1; s2])
     | Eifthenelse, [e1; e2; e3] ->
        let* s1 = iexp is_fun genv env e1 in
        let* s2 = iexp is_fun genv env e2 in
        let* s3 = iexp is_fun genv env e3 in
        return (Slist [s1; s2; s3])
     | Eseq, [e1; e2] ->
        let* s1 = iexp is_fun genv env e1 in
        let* s2 = iexp is_fun genv env e2 in
        return (Slist [s1; s2])
     | Erun _, [{ e_loc = e_loc1} as e1; e2] ->
        (* node instanciation. [e1] must be a static expression *)
        if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
        else 
          (* [e1] is evaluated statically *)
          let* v = vexp genv env e1 in
          let* v = Primitives.pvalue v |>
                   Opt.to_result ~none: { kind = Etype; loc = e_loc1} in
          let* v =
            Primitives.get_node v |>
            Opt.to_result ~none: { kind = Eshould_be_a_node; loc = e_loc1} in
          let* si = instance e_loc1 v in
          let* s2 = iexp is_fun genv env e2 in
          return (Slist [Sinstance(si); s2])
     | (Eatomic | Etest), [e] -> iexp is_fun genv env e
     | Edisc, [e] -> 
       if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
       else iexp is_fun genv env e
     | Eup _, [e] ->
        if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
        else let* s = iexp is_fun genv env e in
          return
            (Slist [Szstate { zin = false; zout = max_float }; s])
     | Eperiod, [e1; e2] ->
       (* [e1] and [e2] must be static *)
       if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
        else let* v1 = vexp genv env e1 in
          let* v2 = vexp genv env e2 in
          let* v1 = is_vfloat v1 |>
                    Opt.to_result ~none: { kind = Etype; loc = e_loc} in
          let* v2 = is_vfloat v2 |>
                    Opt.to_result ~none: { kind = Etype; loc = e_loc} in
          return
            (Speriod
               { zin = false; phase = v1; period = v2; horizon = v1 +. v2 })
     | Earray _, e_list ->
         let* s_list = map (iexp is_fun genv env) e_list in
         return (Slist s_list)
     | _ -> error { kind = Etype; loc = e_loc }
     end
  | Etuple(e_list) ->
     let* s_list = map (iexp is_fun genv env) e_list in
     return (Slist(s_list))
  | Eapp { f = { e_desc = Eglobal { lname }; e_loc = l_loc }; arg_list = [e] } ->
     (* When [lname] is a global value, it can denote either a *)
     (* combinatorial function or a node; that is if [f] is a node *)
     (* [f e] is a shortcut for [run f e] *)
     let* v =
       find_gvalue_opt lname genv |>
         Opt.to_result ~none: { kind = Eunbound_lident(lname); loc = l_loc } in
     let* se = iexp is_fun genv env e in
     let* s =
       match v with
       | Vclosure ({ c_funexp = { f_kind = Knode _; f_args = [_] } } as c) ->
          (* [f e] with [f] a node is a short-cut for [run f e] *)
          if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
          else let* si = instance l_loc c in
            return (Sinstance(si))
       | Vclosure _ | Vfun _ -> return Sempty
       | _ -> error { kind = Etype; loc = e_loc } in
     return (Slist [s; se])
  | Eapp { f; arg_list } ->
     let* s = iexp is_fun genv env f in
     let* s_list = map (iexp is_fun genv env) arg_list in
     return (Slist(s :: s_list))
  | Esizeapp { f } -> 
     let* s = iexp is_fun genv env f in return s
  | Elet(leq, e) ->
     let* l_env, s_eq = ileq is_fun genv env leq in
     let* se = iexp is_fun genv (Env.append l_env env) e in
     return (Slist [s_eq; se])
  | Elocal(b_eq, e) ->
     let* s_b_eq = iblock is_fun genv env b_eq in
     let* se = iexp is_fun genv env e in
     return (Slist [s_b_eq; se])
  | Erecord_access({ arg }) ->
     iexp is_fun genv env arg
  | Erecord(r_list) ->
     let* s_list = map (fun { arg } -> iexp is_fun genv env arg) r_list in
     return (Slist(s_list))
  | Erecord_with(e, r_list) ->
     let* se = iexp is_fun genv env e in
     let* s_list = map (fun { arg } -> iexp is_fun genv env arg) r_list in
     return (Slist(se :: s_list))
  | Etypeconstraint(e, _) -> iexp is_fun genv env e
  | Efun _ -> return Sempty
  | Ematch { is_size; e; handlers } ->
     (* if [is_size] then evaluate the corresponding branch *)
     (* the initial state is that of the selected branch *)
     let* se = iexp is_fun genv env e in
     if is_size then
       (* evaluate the size; the result must be an integer *)
       let* ve = vsexp genv env e se in
       let* v = is_int e.e_loc ve in
       let* sm =
         Match.match_handler_list 
           e_loc (iexp is_fun) genv env (Vint(v)) handlers in
       return (Slist [Sstatic(Vint(v)); sm])
     else
       let* s_handlers = map (imatch_handler is_fun iexp genv env) handlers in
     return (Slist (se :: s_handlers))
  | Epresent { handlers; default_opt } ->
     let* s_handlers =
       map (ipresent_handler is_fun iscondpat iexp genv env) handlers in
     let* s_default_opt = idefault_opt is_fun iexp genv env default_opt in
     return (Slist (s_default_opt :: s_handlers))
  | Ereset(e_body, e_res) ->
     (* a reset is allowed only in a statefull expression *)
     if is_fun then error { kind = Eshould_be_combinatorial; loc = e_loc }
     else let* s_body = iexp is_fun genv env e_body in
       let* s_res = iexp is_fun genv env e_res in
       (* TODO: double the state; an idea from Louis Mandel *)
       (* in case of a reset, simply restart from this copy *)
       (* The alternative (and current) solution recalls function [iexp] *)
       (* In the generated code produced by a compiler, this code is *)
       (* statically scheduled. The reset is obtained by calling a reset method *)
    (* which set state variable to their initial value *)
       return (Slist[s_body; s_res])
  | Eassert(e_body) ->
     let* s_body = iexp is_fun genv env e_body in
     return s_body
  | Eforloop({ for_size; for_kind; for_input; for_body; for_resume }) ->
     let* si_list = map (ifor_input is_fun genv env) for_input in
     let* s_body, sr_list = 
         ifor_exp is_fun for_resume genv env for_body in
       let* s_size, s_body =
         ifor_kind genv env for_size for_kind s_body in
       return (Slist (s_size :: Slist(s_body :: sr_list) :: si_list))

and iexp_opt is_fun genv env e_opt =
  match e_opt with | None -> return Sempty | Some(e) -> iexp is_fun genv env e

and ifor_kind genv env for_size for_kind s_body =
  match for_size with
  | None -> return (Sopt(None), s_body)
  | Some({ e_loc } as e) ->
     (* [e] must be a static (hence stateless) expression *)
     let* v = vexp genv env e in
     (* and an integer value *)
     let* v = is_int e_loc v in
     let s_size = Sopt(Some(Value(Vint(v)))) in
     let s_body = ialloc_foreach_loop v for_kind s_body in
     return (s_size, s_body)

(* duplicate the memory [n] times if the loop is a foreach loop *)
and ialloc_foreach_loop size for_kind s_for_body =
  match for_kind with
  | Kforward _ -> (* the while condition must be combinatorial *)
     s_for_body
  | Kforeach -> (* the initial state is a list of states *)
     Slist(Util.list_of size s_for_body)

and ifor_input is_fun genv env { desc; loc } =
  match desc with
  | Einput { e; by } ->
     let* se = iexp is_fun genv env e in
     let* se_opt =
       match by with
       | None -> return Sempty
       | Some(e) ->
          (* [by] must be static and an integer *)
          let* v = vexp genv env e in
          let* v = is_int e.e_loc v in
          return (Sval(Value(Vint(v)))) in
     return (Slist [se; se_opt])
  | Eindex { e_left; e_right } ->
     let* s1 = iexp is_fun genv env e_left in
     let* s2 = iexp is_fun genv env e_right in
     return (Slist [s1; s2])

and ifor_output is_fun is_resume genv env { desc = { for_init; for_default }; loc } =
  let* s_init =
    match for_init with
    | None -> return Sempty
    | Some(e) -> 
       (* if [is_resume = false] that is, the iteration restarts from *)
       (* the initial state then the state variable [last x] is allowed *)
       if is_fun && is_resume then error { kind = Eshould_be_combinatorial; loc } 
       else 
         let* s_e = iexp is_fun genv env e in
         (* allocate a memory for storing [last x] *)
         return (Slist [Sopt(None); s_e]) in
  let* s_default = iexp_opt is_fun genv env for_default in
  return (Slist [s_init; s_default])

and ifor_vardec is_fun is_resume genv env { desc = { for_vardec } } =
  ivardec is_fun is_resume genv env for_vardec

(* if the for loop is a forward iteration that is reset *)
(* the overal code is considered to be combinational whereas the body *)
(* can be stateful *)
and ifor_exp is_fun is_resume genv env r =
  match r with
  | Forexp { exp } ->
     let* s = iexp (is_fun && is_resume) genv env exp in
     return (s, [])
  | Forreturns { r_returns; r_block } ->
     let* sr_list = map (ifor_vardec is_fun is_resume genv env) r_returns in
     let* s_b = iblock (is_fun && is_resume) genv env r_block in
     return (s_b, sr_list)

(* initial state of an equation *)
and ieq is_fun genv env { eq_desc; eq_loc  } =
  match eq_desc with
  | EQeq(_, e) -> iexp is_fun genv env e
  | EQsizefun _ -> return Sempty
  | EQder { e; e_opt; handlers } ->
     (* [x becomes an input; x' an output] *)
     (* they are stored as a state { der = x'; pos = x } *)
     let* se = iexp is_fun genv env e in
     let* s0 = iexp_opt is_fun genv env e_opt in
     let* sp_h_list =
       map (ipresent_handler is_fun iscondpat iexp genv env) handlers in
     return
       (Slist
          (Scstate { pos = zero_float; der = zero_float } ::
             se :: s0 :: sp_h_list))
  | EQinit(_, e) ->
     let* se = iexp is_fun genv env e in
     return (Slist [Sopt(None); se])
  | EQemit(_, e_opt) ->
     iexp_opt is_fun genv env e_opt
  | EQif { e; eq_true; eq_false } ->
     let* se = iexp is_fun genv env e in
     (* try to evaluate [se] statically *)
     let* v = try_vsexp genv env e se in
     let* s = match v with 
       | None -> 
          let* seq_true = ieq is_fun genv env eq_true in
          let* seq_false = ieq is_fun genv env eq_false in
          return (Slist [se; seq_true; seq_false])
       | Some(b) ->
          let* v = is_bool b |> 
                   Opt.to_result ~none:{ kind = Etype; loc = e.e_loc } in
          if v then let* seq_true = ieq is_fun genv env eq_true in
            return (Slist [Sstatic(Vbool(true)); seq_true; Sempty])
          else let* seq_false = ieq is_fun genv env eq_false in
          return (Slist [Sstatic(Vbool(false)); Sempty; seq_false]) in
     return s
  | EQand { eq_list } ->
     let* seq_list = map (ieq is_fun genv env) eq_list in
     return (Slist seq_list)
  | EQlocal(b_eq) ->
     let* s_b_eq = iblock is_fun genv env b_eq in
     return s_b_eq
  | EQlet(leq, eq) ->
     let* l_env, s_leq = ileq is_fun genv env leq in
     let* s_eq = ieq is_fun genv (Env.append l_env env) eq in
     return (Slist [s_leq; s_eq])
  | EQreset(eq, e) ->
     let* s_eq = ieq is_fun genv env eq in
     let* se = iexp is_fun genv env e in
     return (Slist [s_eq; se])
  | EQpresent { handlers; default_opt } ->
     let* s_list =
       map (ipresent_handler is_fun iscondpat ieq genv env) handlers in
     let* s_default_opt = idefault_opt is_fun ieq genv env default_opt in
     return (Slist (s_default_opt :: s_list))
  | EQautomaton { handlers; state_opt } ->
     if is_fun then 
       error { kind = Eshould_be_combinatorial; loc = eq_loc }
     else let* s_list = map (iautomaton_handler is_fun genv env) handlers in
       (* The initial state is the first in the list *)
       (* if no initialisation code is given *)
       let* a_h =
         List.nth_opt handlers 0 |>
         Opt.to_result ~none:{ kind = unexpected_failure; loc = eq_loc } in
       let* i, si = initial_state_of_automaton is_fun genv env a_h state_opt in
       (* two state variables: initial state of the automaton and reset bit *)
       return (Slist(i :: Sval(Value(Vbool(false))) :: si :: s_list))
  | EQmatch { is_size; e; handlers } ->
     (* if [is_size] then evaluate the corresponding branch *)
     (* the initial state is that of the selected branch *)
     let* se = iexp is_fun genv env e in
     if is_size then
       (* evaluate the size; the result must be an integer *)
       let* ve = vsexp genv env e se in
       let* v = is_int e.e_loc ve in
       let* sm =
         Match.match_handler_list 
           eq_loc (ieq is_fun) genv env (Vint(v)) handlers in
       return (Slist [Sstatic(Vint(v)); sm])
     else
       (* the state is a list of states - one per hander *)
       let* sm_list = map (imatch_handler is_fun ieq genv env) handlers in
       return (Slist (se :: sm_list))
  | EQempty -> return Sempty
  | EQassert(e) ->
     let* se = iexp is_fun genv env e in
     return se
  | EQforloop({ for_size; for_kind; for_input;
                for_body = { for_out; for_block }; for_resume }) ->
     (* if the size is not given there should be at least one input *)
     match for_size, for_input with
     | None, [] -> error { kind = Eloop_cannot_determine_size; loc = eq_loc }
     | _ ->
        (* if the for loop is a forward iteration that is reset *)
        (* the overal code is considered to be combinational whereas the body *)
        (* can be stateful *)
        let* s_input_list = map (ifor_input is_fun genv env) for_input in
        let* so_list = 
          map (ifor_output is_fun for_resume genv env) for_out in
        let* s_body = iblock (is_fun && for_resume) genv env for_block in
        let* s_size, s_body =
          ifor_kind genv env for_size for_kind s_body in
        return (Slist (s_size :: Slist (s_body :: so_list) :: s_input_list))

and iblock is_fun genv env { b_vars; b_body } =
  let* s_b_vars = map (ivardec is_fun true genv env) b_vars in
  let* s_b_body = ieq is_fun genv env b_body in
  return (Slist (s_b_body :: s_b_vars))

(* initial state of a variable declaration *)
(* if [is_resume = false] that is, the iteration always restarts from *)
(* the initial state then [last x] and the initialization [... init ...] *)
(* is allowed even when [is_fun = true] *)
and ivardec is_fun is_resume genv env 
    { var_init; var_default; var_loc; var_is_last } =
  let* s_init =
    match var_init with
    | None -> 
       (* [last x] is only allowed *)
       (* when [is_fun = false] or [is_resume = false] *)
       if var_is_last then
         if is_fun && is_resume then 
           error { kind = Eshould_be_combinatorial; loc = var_loc }
         else return (Sval(Vnil)) else return Sempty
    | Some(e) ->
       (* a state is necessary to store the previous value *)
       (* it is possible only if [if_fun = false] or [is_resume = false] *)
       if is_fun && is_resume then 
         error { kind = Eshould_be_combinatorial; loc = var_loc }
       else 
         let* s = iexp is_fun genv env e in return (Slist [Sopt(None); s]) in
  let* s_default =
    match var_default with
    | None -> return Sempty
    | Some(e) -> iexp is_fun genv env e in
  return (Slist [s_init; s_default])

and iautomaton_handler is_fun genv env { s_let; s_body; s_trans } =
  let* l_env, s_list = ileq_list is_fun genv env s_let in
  let* s_body = iblock is_fun genv (Env.append l_env env) s_body in
  let* st_list = map (iescape is_fun genv env) s_trans in
  return (Slist [Slist(s_list); s_body; Slist(st_list)])

and ileq_list is_fun genv env leq_list =
  mapfold 
    (fun acc_env leq ->
       let* l_env, s = ileq is_fun genv (Env.append acc_env env) leq in
       return (Env.append l_env acc_env, s))
    Env.empty leq_list
  
(* initial state of a local declaration [let eq in e] *)
and ileq is_fun genv env ({ l_kind; l_eq; l_rec } as leq) =
  match l_kind with
  | Kconst | Kstatic ->
     (* if the declaration is constant/static, its value is computed during *)
     (* the initialization phase *)
     let* l_env = vleq genv env leq in
     return (l_env, Senv(l_env))
  | Kany ->
     let* s = ieq is_fun genv env l_eq in
     return (Env.empty, s)

(* initial state of an automaton *)
and initial_state_of_automaton 
    is_fun genv env { s_state = { desc; loc } } state_opt =
  match state_opt with
  | None ->
     (* no initial state is given. The initial state is the first *)
     (* in the list *)
     let* i = match desc with
       | Estate0pat(f) -> return (Sval(Value(Vstate0(f))))
       | Estate1pat(f, _) ->
          error { kind = Einitial_state_with_parameter(f); loc } in
     return (i, Sempty)
  | Some(state) ->
     let* s = istate is_fun genv env state in
     return (Sopt(None), s)

and iescape is_fun genv env { e_cond; e_let; e_body; e_next_state } =
  let* s_cond = iscondpat is_fun genv env e_cond in
  let* l_env, s_list = ileq_list is_fun genv env e_let in
  let* s_body = iblock is_fun genv env e_body in
  let* s_state = istate is_fun genv env e_next_state in
  return (Slist [s_cond; Slist(s_list); s_body; s_state])

and iscondpat is_fun genv env { desc } =
  match desc with
  | Econdand(sc1, sc2) | Econdor(sc1, sc2) ->
     let* s1 = iscondpat is_fun genv env sc1 in
     let* s2 = iscondpat is_fun genv env sc2 in
     return (Slist [s1; s2])
  | Econdexp(e_cond) ->
     iexp is_fun genv env e_cond
  | Econdpat(e, p) ->
     let* se = iexp is_fun genv env e in
     return se
  | Econdon(sc, e) ->
     let* s_sc = iscondpat is_fun genv env sc in
     let* se = iexp is_fun genv env e in
     return (Slist [s_sc; se])

and istate is_fun genv env { desc } =
  match desc with
  | Estate0 _ -> return Sempty
  | Estate1(_, e_list) ->
     let* s_list = map (iexp is_fun genv env) e_list in
     return (Slist(s_list))
  | Estateif(e, s1, s2) ->
     let* se = iexp is_fun genv env e in
     let* se1 = istate is_fun genv env s1 in
     let* se2 = istate is_fun genv env s2 in
     return (Slist[se; se1; se2])

and iresult is_fun genv env { r_desc } =
  match r_desc with
  | Exp(e) -> iexp is_fun genv env e
  | Returns(b) -> iblock is_fun genv env b

(* an instance of a node *)
and instance loc ({ c_funexp = { f_args; f_body }; c_genv; c_env } as c) =
  match f_args with
  | [ arg ] ->
     let* s_list = map (ivardec false true c_genv c_env) arg in
     let* s_body = iresult false c_genv c_env f_body in
     return { init = Slist (s_body :: s_list); step = c }
  | _ -> error { kind = Etype; loc }

(* The main step function *)
(* the value of an expression [e] in a global environment [genv] and local *)
(* environment [env] is a step function. *)
(* Its type is [state -> (value * state) option] *)
and sexp genv env { e_desc; e_loc } s =
  match e_desc, s with
  | _, Sbot -> return (Vbot, s)
  | _, Snil -> return (Vnil, s)
  | _, Sstatic(v) -> return (Value(v), s)
  | Econst(v), Sempty ->
     return (Value (immediate v), s)
  | Econstr0 { lname }, Sempty ->
     return (Value (Vconstr0(lname)), s)
  | Evar x, Sempty ->
     let* v =
       find_value_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = e_loc } in
     return (v, s)
  | Eglobal { lname }, Sempty ->
     let* v =
       find_gvalue_opt lname genv |>
         Opt.to_result ~none:{ kind = Eunbound_lident(lname); loc = e_loc } in
     return (Value(v), s)
  | Elast { id }, Sempty ->
     let* v =
       find_last_opt id env  |>
         Opt.to_result ~none:{ kind = Eunbound_last_ident(id); loc = e_loc } in
     return (v, s)
  | Eop(op, e_list), s ->
     begin match op, e_list, s with
     | (* initialized unit-delay with a constant *)
       Efby, [_; e2], Slist [Sval(v); s2] ->
        let* v2, s2 = sexp genv env e2 s2  in
        return (v, Slist [Sval(v2); s2])
     | Efby, [e1; e2], Slist [Sopt(v_opt); s1; s2] ->
        let* v1, s1 = sexp genv env e1 s1  in
        let* v2, s2 = sexp genv env e2 s2  in
        (* is-it the first instant? *)
        let v =
          match v_opt with | None -> v1 | Some(v) -> v in
        return (v, Slist [Sopt(Some(v2)); s1; s2])
     | Eunarypre, [e], Slist [Sval(v); s] ->
        let* ve, s = sexp genv env e s in
        return (v, Slist [Sval(ve); s])
     | Eminusgreater, [e1; e2], Slist [Sval(v); s1; s2] ->
        (* when [v = true] this is the very first instant. [v] is a reset bit *)
        let* v1, s1 = sexp genv env e1 s1  in
        let* v2, s2 = sexp genv env e2 s2  in
        let* v_out =
          Primitives.ifthenelse v v1 v2 |>
            Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
        return (v_out, Slist [Sval(Value(Vbool(false))); s1; s2])
     | Eifthenelse, [e1; e2; e3], Slist [s1; s2; s3] ->
        let* v1, s1 = sexp genv env e1 s1 in
        let* v2, s2 = sexp genv env e2 s2 in
        let* v3, s3 = sexp genv env e3 s3 in
        let* v =
          ifthenelse v1 v2 v3 |>
            Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
        return (v, Slist [s1; s2; s3])
     | Eseq, [e1; e2], Slist [s1; s2] ->
        let* _, s1 = sexp genv env e1 s1 in
        let* v2, s2 = sexp genv env e2 s2 in
        return (v2, Slist [s1; s2])
     | Erun _, [_; e], Slist [Sinstance si; s] ->
        (* the application of a n-ary node is of the form [f(e1,..., en)] or *)
        (* [run f (e1,...,en)]. The [ei] are non strict *)
        let* v, s = sarg genv env e s in
        let* v, si = run e_loc si v in
        return (v, Slist [Sinstance si; s])
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
     | Eup _, [e], Slist [Szstate { zin }; s] ->
       (* [zin]: set to true when the solver detect a zero-crossing; *)
       (* [zout]: output to be followed for zero-crossing detection *)
        let* zout, s = sexp genv env e s in
        return (Value(Vbool(zin)),
                Slist [Szstate { zin = false; zout }; s])
     | Eperiod, [_; _], Speriod ({ zin; phase; period; horizon } as p) ->
        (* Semantically: h = present zin -> last h + period init phase+period *)
        let horizon = if zin then horizon +. period else horizon in
        return
          (Value(Vbool(zin)),
           Speriod { p with horizon })
     | Ehorizon, [e], Slist [Shorizon ({ zin; horizon } as h); s] ->
        if zin then
          let* horizon, s = sexp genv env e s in
          match horizon with
          | Vbot -> return (Vbot, Slist [Shorizon(h); s])
          | Vnil -> return (Vnil, Slist [Shorizon(h); s])
          | Value(v) ->
             let* horizon =
               is_float v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
             return
               (Value(Vbool(zin)), Slist [Shorizon { h with horizon }; s])
        else
          return (Value(Vbool(zin)), Slist [Shorizon(h); s])
     | Earray(op), _, _ ->
        begin match op, e_list, s with
          | Econcat, [e1; e2], Slist [s1; s2] ->
             let* v1, s1 = sexp genv env e1 s1 in
             let* v2, s2 = sexp genv env e2 s2 in
             let* v = Arrays.concat e_loc v1 v2 in
             return (v, Slist [s1; s2])
          | Eget, [e; i], Slist [s1; s2] ->
             let* v, s1 = sexp genv env e s1 in
             let* i = vsexp genv env i s2 in
             let* v = Arrays.get e_loc v i in
             return (v, Slist [s1; s2])
          | Eget_with_default, [e; ei; default], Slist [se; si; s_default] ->
             let* v, se = sexp genv env e se in
             let* vi, si = sexp genv env ei si in
             let* default, s_default = sexp genv env default s_default in
             let* v = Arrays.get_with_default e_loc v vi default in
             return (v, s)
          | Eslice, [e; i1; i2], Slist [s; s1; s2] ->
             let* v, s = sexp genv env e s in
             let* i1 = vsexp genv env i1 s1 in
             let* i2 = vsexp genv env i2 s2 in
             let* v = Arrays.slice e_loc v i1 i2 in
             return (v, Slist [s; s1; s2])
          | Eupdate, (e :: arg :: i_list), Slist (s :: s_arg :: s_list) ->
             (* [| e with i1,..., in <- arg |] *)
             let* v, s = sexp genv env e s in
             let* v_arg, s_arg = sexp genv env arg s_arg in
             let* i_list, s_list = slist e_loc genv env sexp i_list s_list in
             let* v = Arrays.update_list e_loc v i_list v_arg in
             return (v, Slist (s :: s_arg :: s_list))
          | Earray_list, e_list, Slist s_list ->
             let* v_list, s_list = slist e_loc genv env sexp e_list s_list in
             let v_list = Primitives.slist v_list in
             return
               (Primitives.lift 
                  (fun v -> Varray(Vflat(Array.of_list v))) v_list,
                Slist s_list)
          | Etranspose, [e], Slist [s] ->
             let* v, s = sexp genv env e s in
             let*v = Arrays.transpose e_loc v in
             return (v, Slist [s])
          | Eflatten, [e], Slist [s] ->
             let* v, s = sexp genv env e s in
             let*v = Arrays.flatten e_loc v in
             return (v, Slist [s])
          | Ereverse, [e], Slist [s] ->
             let* v, s = sexp genv env e s in
             let*v = Arrays.reverse e_loc v in
             return (v, Slist [s])
          | _ -> error { kind = Etype; loc = e_loc }
        end
     | _ -> error { kind = Etype; loc = e_loc }
     end
  | Econstr1 { lname; arg_list }, Slist(s_list) ->
     let* v_list, s_list = sexp_list e_loc genv env arg_list s_list in
     (* check that all component are not nil nor bot *)
     let* v =
       constr1 lname v_list |>
         Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     return (v, Slist(s_list))
  | Etuple(e_list), Slist(s_list) ->
     (* pairs are considered to be strict *)
     let* v_list, s_list = sexp_list e_loc genv env e_list s_list in
     let* v =
       stuple v_list |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     return (v, Slist(s_list))
  | Erecord_access { label; arg }, s ->
     let* v, s = sexp genv env arg s in
     let* v =
       let+ v = v in
       let* v = Records.record_access { label; arg = v } |>
                  Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
       return (Value(v)) in
     return (v, s)
  | Erecord(r_list), Slist(s_list) ->
     let* r_list, s_list =
       slist e_loc genv env
         (fun genv env { label; arg } s ->
           let* v, s = sexp genv env arg s in
           let* v =
             let+ v = v in
             return (Value { label; arg = v }) in
           return (v, s)) r_list s_list in
     let* v =
       srecord r_list |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     return (v, Slist(s_list))
  | Erecord_with(r, r_list), Slist(s :: s_list) ->
     let* v, s = sexp genv env r s in
     let* ext_label_arg_list, s_list =
       slist e_loc genv env
         (fun genv env { label; arg } s ->
           let* v, s = sexp genv env arg s in
           let* v =
             let+ v = v in
             return (Value { label; arg = v }) in
           return (v, s)) r_list s_list in
     let* v =
       let+ v = v in
       let* label_arg_list =
         get_record v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
       let+ ext_label_arg_list = Primitives.slist ext_label_arg_list in
       let* r =
         Records.record_with label_arg_list ext_label_arg_list |>
           Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
       return (Value(Vrecord(r))) in
     return (v, Slist(s :: s_list))
  | Etypeconstraint(e, _), s ->
     sexp genv env e s
  | Eapp { arg_list = [e] }, Slist [Sinstance si; s] ->
     (* Here, [f (e1,..., en)] is a short-cut for [run f (e1,...,en)] *)
     let* v, s = sarg genv env e s in
     let* v, si = run e_loc si v in
     return (v, Slist [Sinstance si; s])
  | Eapp { f; arg_list }, Slist (s :: s_list) ->
     (* [f] must return a combinatorial function *)
     let* fv, s = sexp genv env f s in
     let* v_list, s_list = sarg_list e_loc genv env arg_list s_list in
     (* the application of a combinatorial function is considered to be strict *)
     (* if one element is [bot] return [bot]; if [nil] return [nil] *)
     let* v = 
       let+ fv = fv in apply e_loc fv v_list in
     return (v, Slist (s :: s_list))
  | Esizeapp { f; size_list }, s ->
     (* [size_list] is a list of size; it must be combinational *)
     let* fv, s = sexp genv env f s in
     let* v_list = map (size env) size_list in
     let* v = let+ fv = fv in sizeapply e_loc fv v_list in
     return (v, s)
  | Elet(l_eq, e), Slist [s_eq; s] ->
     let* env_eq, s_eq = sleq genv env l_eq s_eq in
     let env = Env.append env_eq env in
     let* v, s = sexp genv env e s in
     return (v, Slist [s_eq; s])
  | Elocal(b_eq, e), Slist [s_b_eq; s] ->
     let* env, _, s_eq = sblock genv env b_eq s_b_eq in
     let* v, s = sexp genv env e s in
     return (v, Slist [s_eq; s])
  | Efun(fe), s ->
     return (Value(Vclosure { c_funexp = fe; c_genv = genv; c_env = env }), s)
  | Ematch { is_size = true; handlers }, Slist [Sstatic(v_size); s] ->
     (* [match size e with | P1 -> ... | ...] *)
     let* v, s =
       static_match_handler_list e_loc sexp genv env v_size handlers s in
     return (v, Slist [Sstatic(v_size); s])
  | Ematch { e; handlers }, Slist(se :: s_list) ->
     let* ve, se = sexp genv env e se in
     let* v, s_list =
       match ve with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (Vbot, sbot_list s_list)
       | Vnil -> return (Vnil, snil_list s_list)
       | Value(ve) ->
          smatch_handler_list e_loc sexp genv env ve handlers s_list in
     return (v, Slist (se :: s_list))
  | Epresent { handlers; default_opt }, Slist(s :: s_list) ->
     (* present z1 -> e1 | ... | zn -> en [[else|init] e]] *)
     let* v_opt, s_list =
       spresent_handler_list e_loc sscondpat Vbot Vnil
         sexp genv env handlers s_list in
     let* v, s =
       match v_opt, default_opt, s with
       | Some(v), Init(e), Slist [Sopt(None); s] ->
          (* at the first instant, execute the initialization *)
          let* v', s = sexp genv env e s in
          return (v, Slist [Sopt(Some(v')); s])
       | Some(v), _, _ -> return (v, s)
       | None, Else(e), s ->
          (* no handler was selected *)
          let* v, s = sexp genv env e s in return (v, s)
       | None, Init(e), Slist [Sopt(s_opt); s] ->
          (* no handler was selected *)
          let* v, s = sexp genv env e s in
          let* v, s =
            match s_opt with
            | None -> return (v, s) | Some(v) -> return (v, s) in
          return (v, Slist [Sopt(Some(v)); s])
       | _ -> (* error *)
          error { kind = Estate; loc = e_loc } in
     return (v, Slist(s :: s_list))
  | Ereset(e_body, e_res), Slist [s_body; s_res] ->
     let* v, s_res = sexp genv env e_res s_res in
     let* v_body, s_body =
       match v with
       | Vbot -> return (Vbot, Sbot)
       | Vnil -> return (Vnil, Snil)
       | Value(v) ->
          let* v =
            is_bool v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
          (* a reset is possible for all expressions - combinatorial or not *)
          reset (iexp false) sexp genv env e_body s_body v in
     return (v_body, Slist [s_body; s_res])
  | Eassert(e_body), s ->
     let* v, s = sexp genv env e_body s in
     let* r = check_assertion e_loc v void in
     return (r, s)
  | Eforloop ({ for_kind; for_index; for_input; for_body; for_resume }),
    Slist (Sopt(Some(Value(Vint(size)))) as sv ::
             Slist(s_for_body :: sr_list) :: si_list) ->
     (* the size [size] is known *)
     (* computes a local environment for variables names introduced *)
     (* in the index and input list; do it sequentially *)
     let i_env =
       let open Forloop in
       match for_index with
       | None -> Env.empty
       | Some(id) ->
          Env.singleton id (Vindex { ve_left = 0;
                                     ve_right = size - 1; dir = true }) in
     let* i_env, si_list =
       mapfold2v { kind = Estate; loc = e_loc }
         (sfor_input size genv env) i_env for_input si_list in
     (* step in the body only if [i_env] is not bot or nil *)
     let* r, s_for_body_new, sr_list =
       sforloop_exp
         e_loc genv env size for_kind for_resume for_body
         i_env s_for_body sr_list in
     let s_for_body = if for_resume then s_for_body_new
                      else s_for_body in
     return (r, Slist(sv :: Slist(s_for_body :: sr_list) :: si_list))
  | Eforloop ({ for_kind; for_index;
                for_input = input :: input_list; for_body; for_resume }),
    Slist (Sopt(None) :: Slist(s_for_body :: sr_list) ::
             s_input :: s_input_list) ->
     (* the size is not known *)
     let* size_i_env, si =
       sfor_input_no_size genv env Env.empty input s_input in
     (* step in the body only if the input is not bot or nil *)
     let* r, s_size, s_for_body, sr_list, si, si_list =
       match size_i_env with
       | Vbot ->
          return (Vbot, None, s_for_body, sr_list, si, sbot_list s_input_list)
       | Vnil ->
          return (Vnil, None, s_for_body, sr_list, si, snil_list s_input_list)
       | Value(size, i_env) ->
          (* allocate the memory if the loop is a foreach loop *)
          let s_for_body = ialloc_foreach_loop size for_kind s_for_body in
          let i_env =
            let open Forloop in
            match for_index with
            | None -> i_env
            | Some(id) ->
               Env.add id (Vindex { ve_left = 0;
                                    ve_right = size - 1; dir = true }) i_env in
          let* i_env, si_list =
            mapfold2v { kind = Estate; loc = e_loc }
              (sfor_input size genv env) i_env input_list s_input_list in
          (* step in the body only if [i_env] is not bot or nil *)
          let* r, s_for_body_new, sr_list =
            sforloop_exp e_loc genv env size for_kind for_resume for_body i_env
              s_for_body sr_list in
          (* if [for_resume = true] keep the final state *)
          let s_for_body = if for_resume then s_for_body_new
                            else s_for_body in
          return (r, size_of_for_kind for_kind size,
                  s_for_body, sr_list, si, si_list) in
     return (r, Slist (Sopt(s_size) :: Slist(s_for_body :: sr_list) ::
                         si :: si_list))
  | _ -> error { kind = Estate; loc = e_loc }

and sforloop_exp
  loc genv env for_size for_kind for_resume for_body i_env s_for_body sr_list =
  match i_env with
  | Vbot -> return (Vbot, s_for_body, sr_list)
  | Vnil -> return (Vnil, s_for_body, sr_list)
  | Value(i_env) ->
     let* v, s_for_body, sr_list =
       match for_body with
       | Forexp { exp = e; default = d_opt} ->
          (* the default expression must be combinatorial. *)
          let* ve, s_for_body =
            match for_kind, s_for_body with
            | Kforeach, Slist(s_list) ->
               (* parallel loop; every iteration has its own state *)
               let* ve, s_list =
                 Forloop.foreach loc
                   (fun env s -> sexp genv env e s) env i_env s_list in
               return (ve, Slist(s_list))
            | Kforward(None), _ ->
               (* hyperserial loop; the transition function is iterated *)
               (* on the same state *)
               let* default =
                 match d_opt with
                 | None ->
                    (* An error is raised if there is no iteration *)
                    (* and no default value is given *)
                    if for_size <= 0 then
                      error { kind = Eloop_no_iteration; loc }
                    else
                      (* the default value is [nil] *)
                      return Vnil
                 | Some(e) -> vexp genv env e in
               (* the final state is discarded *)
               let* ve, s_for_body_new =
                 Forloop.forward loc (fun env s -> sexp genv env e s)
                   env i_env for_size default s_for_body in
               let s_for_body =
                 if for_resume then s_for_body_new else s_for_body in
               return (ve, s_for_body)
            | _ -> error { kind = Estate; loc } in
          return (ve, s_for_body, sr_list)
       | Forreturns { r_returns; r_block } ->
          (* 1/ computes the environment from the [returns] *)
          (* environment [env_v + acc_env]. Vars in [acc_env] *)
          (* are accumulated values such that *)
          (* [acc_env(last x)(i) = acc_env(x)(i-1)] where [i] is the *)
          (* iteration index. *)
          let* acc_env, sr_list =
            mapfold3 { kind = Estate; loc }
              (sfor_vardec genv env) Env.empty r_returns sr_list
              (bot_list r_returns) in
          (* 2/ runs the body *)
          let* missing, env_list, acc_env, s_for_body =
            match for_kind, s_for_body with
            | Kforeach, Slist(s_list) ->
               let sbody env acc_env s =
                 sforblock genv env acc_env r_block None s in
               let* env_list, acc_env, s_list =
                 Forloop.foreach_eq loc
                   sbody env i_env acc_env s_list in
               return (0, env_list, acc_env, Slist(s_list))
            | Kforward(exit), _ ->
               let sbody env acc_env s =
                 sforblock genv env acc_env r_block exit s in
               let* env_list, acc_env, s_for_body_new =
                 Forloop.forward_eq loc
                   sbody env i_env acc_env for_size s_for_body in
               (* was-it a complete iteration? *)
               let missing = for_size - List.length env_list in
               let s_for_body =
                 if for_resume then s_for_body_new else s_for_body in
               return (missing, env_list, acc_env, s_for_body)
            | _ -> error { kind = Estate; loc } in
          (* store the next last value for [returns] - only necessary *)
          (* when [resume = true] *)
          let* sr_list = 
            if for_resume then
              map2 { kind = Estate; loc } 
                (set_forexp_out acc_env) r_returns sr_list
            else return sr_list in
          (* return the result of the for loop *)
          let* v = for_matching_out missing env_list acc_env r_returns in
          return (v, s_for_body, sr_list) in
     return (v, s_for_body, sr_list)

and sexp_opt genv env e_opt s =
  match e_opt with
  | None -> return (None, s)
  | Some(e) -> let* v, s = sexp genv env e s in return (Some(v), s)

and sexp_init_opt loc genv env e_opt s =
  (* compute [last x] *)
  match e_opt, s with
  | None, _ -> return (None, s)
  | Some(e), Slist [Sopt(v_opt); s] ->
     let* ve, s = sexp genv env e s in 
     let* v_opt, s_opt = match v_opt with
       | None -> (* first instant *)
          return (Some(ve), None)
       | Some(v) -> (* return the stored value *)
          return (Some(v), v_opt) in
     return (v_opt, Slist [Sopt(s_opt); s])
  | _ -> error { kind = Estate; loc }
        
(* computing the value of an expression with a given state *)
(* the expression [e] is expected to be combinational *)
and vsexp genv env e s =
  let* v, _ = sexp genv env e s in
  return v

(* try to evaluate e. Return None if some variables are unbounded; Some(v) *)
(* if the execution succeed; propagate the error otherwise *)
and try_vsexp genv env e s =
  let v = vsexp genv env e s in
  match v with 
  | Error({ kind = Eunbound_ident _ | Eunbound_last_ident _ }) -> return None
  | Error(k) -> error k
  | Ok(v) -> 
     match v with | Vbot | Vnil -> return None | Value(v) -> return (Some(v))

and try_vexp genv env e =
  let v = vexp genv env e in
  match v with 
  | Error({ kind = Eunbound_ident _ | Eunbound_last_ident _ }) -> return None
  | Error(k) -> error k
  | Ok(v) -> 
     match v with | Vbot | Vnil -> return None | Value(v) -> return (Some(v))

(* computing the value of an expression from the initial state *)
(* the expression is supposed to be stateless, that is, *)
(* the new state must be unchanged *)
and vexp genv env e =
  let* s = iexp true genv env e in
  vsexp genv env e s

(* computing the environment defined by a local definition *)
(* the expression [l_eq] is expected to be combinational *)
and vleq genv env ({ l_rec; l_eq } as leq) =
  (* for the moment, recursive functions are only allowed when they *)
  (* are size functions *)
  if l_rec then
    let* defs = sizefun_defs genv env leq in
    return (Fix.sizefixpoint defs)
  else let* s = ieq true genv env l_eq in
    let* env, _ = seq genv env l_eq s in
    return env

(* computing the value of a result combinatorial expression *)
and vresult genv env r =
  let* s = iresult true genv env r in
  let* v, _ = sresult genv env r s in
  return v

and sfor_vardec genv env acc_env { desc = { for_vardec } } s v =
  svardec genv env acc_env for_vardec s v

(* compute the initial value of accumulated variables *)
(* when { for_name = xi; for_init = v } returns *)
(*                       [xi = { cur = bot; last = v; default = None }] *) 
(* when { for_name = xi; for_init = v; for_default = d } returns *)
(*                       [xi = { cur = bot; last = v; default = d }] *)
(* otherwise [xi = { cur = bot; last = None; default = None }] *)
and sfor_out genv env acc_env
  { desc = { for_name; for_init; for_default }; loc } s =
  match s with
  | Slist [s_init; s_default] ->
     let* last, s_init = sexp_init_opt loc genv env for_init s_init in
     let* default, s_default = sexp_opt genv env for_default s_default in
     return
       (Env.add for_name { empty with cur = Some Vbot; last; default } acc_env,
        Slist [s_init; s_default])
  | _ -> error { kind = Estate; loc}

(* evaluate an index returns a local environment *)
and sfor_input size genv env i_env { desc; loc } s =
  let open Forloop in
  match desc, s with
  | Einput { id; e; by = None }, Slist [se; se_opt] ->
     (* [id in e] means that in iteration [i], [id = e.(i)] *)
     let* ve, se = sexp genv env e se in
     let* entry = input loc ve None in
     let* i_env =
       let+ a_size, entry = entry in
       if a_size = size
       then return (Value(Env.add id entry i_env))
       else
         error { kind = Earray_size { size = a_size; index = size }; loc } in
     return (i_env, Slist [se; se_opt])
  | Einput { id; e; by = Some _ }, Slist [se; Sval(Value(Vint(k)))] ->
     (* [id in e by k] means that in iteration [i], [id = e.(k * i)] *)
     (* [k] must be static *)
     let* ve, se = sexp genv env e se in
     let* entry = input loc ve (Some(k)) in
     let* i_env =
       let+ a_size, entry = entry in
       if a_size = size * k
       then return (Value(Env.add id entry i_env))
       else
         error
           { kind = Earray_size { size = a_size; index = size * k }; loc } in
     return (i_env, Slist [se; Sval(Value(Vint(k)))])
  | Eindex { id; e_left; e_right; dir }, Slist [se_left; se_right] ->
     let* ve_left, se_left = sexp genv env e_left se_left in
     let* ve_right, se_right = sexp genv env e_right se_right in
     let* entry = index loc ve_left ve_right dir in
     let* i_env =
       let+ a_size, entry = entry in
       if a_size = size
       then return (Value(Env.add id entry i_env))
       else error { kind = Earray_size { size; index = a_size }; loc } in
     return (i_env, Slist [se_left; se_right])
  | _ ->
     error { kind = Estate; loc }

(* evaluate an index returns a local environment *)
and sfor_input_no_size genv env i_env { desc; loc } s =
  let open Forloop in
  match desc, s with
  | Einput { id; e; by = None }, Slist [se; se_opt] ->
     (* [id in e] means that in iteration [i], [id = e.(i)] *)
     let* ve, se = sexp genv env e se in
     let* entry = input loc ve None in
     let* size_i_env =
       let+ a_size, entry = entry in
       return (Value(a_size, Env.add id entry i_env)) in
      return (size_i_env, Slist [se; se_opt])
  | Einput { id; e; by = Some _ }, Slist [se; (Sval(Value(Vint(k))) as sv)] ->
     (* [id in e by k] means that in iteration [i], [id = e.(k * i)] *)
     (* [k] must be static *)
     let* ve, se = sexp genv env e se in
     let* entry = input loc ve (Some(k)) in
     let* size_i_env =
       let+ a_size, entry = entry in
       let r = a_size mod k in
       let* size =
         if r = 0 then return (a_size / k)
         else
           error
             { kind = Earray_size { size = a_size; index = a_size + r };
               loc } in
       return (Value(size, Env.add id entry i_env)) in
     return (size_i_env, Slist [se; sv])
  | Eindex { id; e_left; e_right; dir }, Slist [se_left; se_right] ->
     let* ve_left, se_left = sexp genv env e_left se_left in
     let* ve_right, se_right = sexp genv env e_right se_right in
     let* entry = index loc ve_left ve_right dir in
     let* i_env =
       let+ a_size, entry = entry in
       return (Value(a_size, Env.add id entry i_env)) in
     return (i_env, Slist [se_left; se_right])
  | _ ->
     error { kind = Estate; loc }

(* a function can take a tuple that is non strict *)
and sarg genv env ({ e_desc; e_loc } as e) s =
  match e_desc, s with
  | Etuple(e_list), Slist(s_list) ->
     let* v_list, s_list = sexp_list e_loc genv env e_list s_list in
     return (Value(Vtuple(v_list)), Slist(s_list))
  | _ ->
     sexp genv env e s

(* application of a node *)
and run loc { init; step } v =
  let* v, init = runstep loc init step v in
  return (v, { init; step })

and runstep loc s { c_funexp = { f_args; f_body }; c_genv; c_env } v =
  let match_in_list a_list s_list v_list =
    let match_in acc vdec s v =
      let* acc, s = svardec c_genv c_env acc vdec s v in
      let* s = set_vardec acc vdec s in
      return (acc, s) in
    mapfold3 { kind = Epattern_matching_failure; loc }
      match_in Env.empty a_list s_list v_list in

  match f_args, s with
  | [arg_list], Slist (s_body :: s_arg_list) ->
     let* v_list =
       (* special case for a single argument *)
       match arg_list with
       | [_] -> let* v =
                  Primitives.atomic v |>
                    Opt.to_result ~none:{ kind = Etype; loc } in
                return [v]
       | _ -> return (Primitives.list_of v) in
     let* env_arg_list, s_arg_list =
       match_in_list arg_list s_arg_list v_list in
     let env = Env.append env_arg_list c_env in
     let* r, s_body = sresult c_genv env f_body s_body in
     return (r, Slist (s_body :: s_arg_list))
  | _ ->
     error { kind = Etype; loc }

and sexp_list loc genv env e_list s_list =
  slist loc genv env sexp e_list s_list

and sarg_list loc genv env e_list s_list =
  slist loc genv env sarg e_list s_list

and sleq genv env { l_kind; l_rec; l_eq = ({ eq_write } as l_eq); l_loc } s_eq =
  match l_kind, s_eq with
  | (Kconst | Kstatic), Senv(l_env) ->
     return (l_env, s_eq)
  | Kany, _ ->
     if l_rec then
       (* Either it is a collection of mutually recursive functions *)
       (* parameterized by a size or stream values *)
       let* defs = sizefun_defs_or_values genv env l_eq in
       let* (env_eq, s_eq) =
         match defs with
         | Either.Right(defs) ->
            let env = Fix.sizefixpoint defs in
            return (env, s_eq)
         | Either.Left(l_eq) ->
            (* compute a bounded fix-point in [n] steps *)
            let bot = Match.bot_env eq_write in
            let n = (Fix.size l_eq) + 1 in
            let* env_eq, s_eq = Fix.eq genv env seq l_eq n s_eq bot in
            (* a dynamic check of causality: all defined names in [eq] *)
            (* must be non bottom provided that all free vars. are non bottom *)
            let* _ = Fix.causal l_loc env env_eq (names eq_write) in
            return (env_eq, s_eq) in
       return (env_eq, s_eq)
     else
       seq genv env l_eq s_eq
  | _ -> error { kind = Estate; loc = l_loc }

and slets loc genv env leq_list s_list =
  mapfold2 { kind = Estate; loc }
    (fun acc leq s -> let* env, s = sleq genv env leq s in
                      return (Env.append env acc, s))
    env leq_list s_list

(* step function for an equation *)
and seq genv env { eq_desc; eq_write; eq_loc } s =
  match eq_desc, s with
  | _, Sbot ->
     return (Match.bot_env eq_write, s)
  | _, Snil ->
     return (Match.nil_env eq_write, s)
  | EQeq(p, e), s ->
     let* v, s = sexp genv env e s in
     let* env_p =
       matcheq v p |>
         Opt.to_result ~none:{ kind = Epattern_matching_failure;
                               loc = eq_loc } in
     return (env_p, s)
  | EQsizefun { sf_id; sf_id_list; sf_e }, s ->
     let v =
       { s_params = sf_id_list; s_body = sf_e; 
         s_genv = genv; s_env = env } in
     return (Env.singleton sf_id (Match.entry (Vsizefun v)), s)
  | EQder { id; e; e_opt; handlers },
    Slist (Scstate({ pos } as sc) :: s :: Sopt(x0_opt) :: s0 :: s_list) ->
     let* ({ last; default } as entry) =
       Env.find_opt id env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(id); loc = eq_loc } in
     (* compute the derivative (w.r.t time) of [x] *)
     let* der, s = sexp genv env e s in
     (* computes the initial position *)
     let* cx0, x0_opt, s0 =
       match e_opt with
       | None ->
          (* [x] should have a default value *)
          let* x0 =
            Fix.default_value last default |>
              Opt.to_result ~none:{ kind = Eno_default(id); loc = eq_loc } in
          return (x0, x0_opt, s0)
       | Some(e0) ->
          match x0_opt with
          | None -> (* first instant *)
             let* x0, s0 = sexp genv env e0 s0 in
             return (x0, Some(x0), s0)
          | Some(x0) -> return (x0, x0_opt, s0) in
     let* cx_opt, s_h_list =
       spresent_handler_list
         eq_loc sscondpat Vbot Vnil sexp genv env handlers s_list in
     let cur =
       match cx_opt with
       | None ->
          (* no reset event; return the value computed by the solver *)
          pos
       | Some(cx) ->
          (* otherwise the value returned by the handler *)
          cx in
     return (Env.singleton id { entry with cur = Some(cur) },
             Slist (Scstate({ sc with der }) :: Sopt(x0_opt) :: s0 :: s_list))
  | EQinit(x, e), Slist [Sopt(None); se] ->
     (* first step *)
     let* v, se = sexp genv env e se in
     let* cur =
       find_value_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = eq_loc } in
     return (Env.singleton x { empty with last = Some(v); reinit = true },
             Slist [Sopt(Some(cur)); se])
  | EQinit(x, e), Slist [Sopt(Some(v)); se] ->
     (* remaining steps *)
     let* cur =
       find_value_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = eq_loc } in
     return (Env.singleton x { empty with last = Some(v); reinit = true },
             Slist [Sopt(Some(cur)); se])
  | EQif { e; eq_true; eq_false }, Slist [se; s_eq_true; s_eq_false] ->
      let* v, se = sexp genv env e se in
      let* env_eq, s_list =
        match v with
        (* if the condition is bot/nil then all variables have value bot/nil *)
        | Vbot -> return (Match.bot_env eq_write, [Sbot; Sbot])
        (* Slist [se; s_eq1; s_eq2]) *)
        | Vnil -> return (Match.nil_env eq_write, [Snil; Snil])
        (* Slist [se; s_eq1; s_eq2]) *)
        | Value(b) ->
           let* v =
             is_bool b |> Opt.to_result ~none:{ kind = Etype; loc = e.e_loc } in
           if v then
             let* env_true, s_eq_true = seq genv env eq_true s_eq_true in
             (* complete the output environment with default *)
             (* or last values from all variables defined in [eq_write] but *)
             (* not in [env1] *)
             let* env_true = Fix.by eq_loc env env_true (names eq_write) in
             return (env_true, [s_eq_true; s_eq_false])
           else
             let* env_false, s_eq_false = seq genv env eq_false s_eq_false in
             (* symetric completion *)
             let* env_false =
               Fix.by eq_loc env env_false (names eq_write) in
             return (env_false, [s_eq_true; s_eq_false]) in
      return (env_eq, Slist (se :: s_list))
  | EQand { eq_list }, Slist(s_list) ->
     let seq genv env acc eq s =
       let* env_eq, s = seq genv env eq s in
       let* acc = merge eq_loc env_eq acc in
       return (acc, s) in
     let* env_eq, s_list =
       mapfold2 { kind = Estate; loc = eq_loc }
         (seq genv env) Env.empty eq_list s_list in
     return (env_eq, Slist(s_list))
  | EQreset(eq, e), Slist [s_eq; se] ->
     let* v, se = sexp genv env e se in
     let* env_eq, s_eq =
       match v with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (Match.bot_env eq_write, Slist [s_eq; se])
       | Vnil -> return (Match.nil_env eq_write, Slist [s_eq; se])
       | Value(v) ->
          let* v =
            is_bool v |> Opt.to_result ~none:{ kind = Etype; loc = e.e_loc } in
          (* a reset is possible for combinatorial or stateful expressions *)
          reset (ieq false) seq genv env eq s_eq v in
     return (env_eq, Slist [s_eq; se])
  | EQlocal(b_eq), s_eq ->
     let* _, env_visible, s_eq = sblock genv env b_eq s_eq in
     return (env_visible, s_eq)
  | EQlet(leq, eq), Slist [s_leq; s_eq] ->
     let* env_eq, s_leq = sleq genv env leq s_leq in
     let env = Env.append env_eq env in
     let* env_local, s_eq = seq genv env eq s_eq in
     return (env_local, Slist [s_leq; s_eq])
  | EQautomaton { is_weak; handlers; state_opt },
    Slist (ps :: Sval(pr) :: si :: s_list) ->
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
          return (Match.bot_env eq_write, ps, pr, s_list)
       | (Vnil, _) | (_, Vnil) ->
          return (Match.nil_env eq_write, ps, pr, s_list)
       | Value(ps), Value(pr) ->
          let* pr =
            is_bool pr |> Opt.to_result ~none:{ kind = Etype; loc = eq_loc } in
          sautomaton_handler_list eq_loc
            is_weak genv env eq_write handlers ps pr s_list in
     return (env, Slist (Sval(ns) :: Sval(nr) :: si :: s_list))
  | EQmatch { is_size = true; e; handlers }, Slist [Sstatic(v_size); s] ->
     (* [match size e with | P1 -> ... | ...] *)
     let* env_handler, s =
       static_match_handler_list eq_loc seq genv env v_size handlers s in
     (* complete missing entries in the environment *)
     let* env_handler = Fix.by eq_loc env env_handler (names eq_write) in
     return (env_handler, Slist [Sstatic(v_size); s])
  | EQmatch { e; handlers }, Slist (se :: s_list) ->
     let* ve, se = sexp genv env e se in
     let* env, s_list =
       match ve with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (Match.bot_env eq_write, s_list)
       | Vnil -> return (Match.nil_env eq_write, s_list)
       | Value(ve) ->
          let* env_handler, s_list =
            smatch_handler_list eq_loc seq genv env ve handlers s_list in
          (* complete missing entries in the environment *)
          let* env_handler = Fix.by eq_loc env env_handler (names eq_write) in
          return (env_handler, s_list) in
     return (env, Slist (se :: s_list))
  | EQpresent { handlers; default_opt }, Slist(s :: s_list) ->
     (* present z1 -> eq1 | ... | zn -> eqn [else eq] *)
     let* env_handler_opt, s_list =
       spresent_handler_list eq_loc
         sscondpat (Match.bot_env eq_write) (Match.nil_env eq_write)
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
          (* this case should not arrive because it is syntactically *)
          (* incorrect *)
          error { kind = unexpected_failure; loc = eq_loc } in
     (* complete missing entries in the environment *)
     let* env_handler = Fix.by eq_loc env env_handler (names eq_write) in
     return (env_handler, Slist (s :: s_list))
  | EQempty, s -> return (Env.empty, s)
  | EQassert(e), s ->
     let* ve, s = sexp genv env e s in
     let* r = check_assertion eq_loc ve Env.empty in
     return (r, s)
  | EQforloop({ for_kind; for_index; for_input; for_body; for_resume }),
    Slist ((Sopt(Some(Value(Vint(size)))) as sv) ::
             Slist(s_for_block :: so_list) :: si_list) ->
     (* the size is known *)
     (* computes a local environment for variables introduced *)
     (* in the index list *)
     let i_env =
       let open Forloop in
       match for_index with
       | None -> Env.empty
       | Some(id) ->
          Env.singleton id (Vindex { ve_left = 0;
                                     ve_right = size - 1; dir = true }) in
     let* i_env, si_list =
       mapfold2v { kind = Estate; loc = eq_loc }
         (sfor_input size genv env) i_env for_input si_list in
     (* step in the body only if [i_env] is not bot or nil *)
     let* r, s_for_block_new, so_list =
       sforloop_eq
         eq_loc genv env size for_kind for_resume for_body
         i_env s_for_block so_list in
     let s_for_block = if for_resume then s_for_block_new
                            else s_for_block in
     return (r, Slist(sv :: Slist(s_for_block :: so_list) :: si_list))
  | EQforloop ({ for_kind; for_index;
                 for_input = input :: input_list; for_body; for_resume }),
    Slist (Sopt(None) :: Slist(s_for_block :: so_list) :: si :: si_list) ->
    (* the size is not known. *)
    let* size_i_env, si =
       sfor_input_no_size genv env Env.empty input si in
    let* r, s_size, s_for_body, so_list, si, si_list =
      match size_i_env with
      | Vbot ->
         return 
           (Match.bot_env eq_write, None, s_for_block, so_list, si, si_list)
      | Vnil ->
         return 
           (Match.nil_env eq_write, None, s_for_block, so_list, si, si_list)
      | Value(size, i_env) ->
         (* allocate the memory if the loop is a foreach loop *)
          let s_for_body = ialloc_foreach_loop size for_kind s_for_block in
          let i_env =
            let open Forloop in
            match for_index with
            | None -> i_env
            | Some(id) ->
               Env.add id (Vindex { ve_left = 0;
                                    ve_right = size - 1; dir = true }) i_env in
          let* i_env, si_list =
           mapfold2v { kind = Estate; loc = eq_loc }
             (sfor_input size genv env) i_env input_list si_list in
         (* step in the body only if [i_env] is not bot or nil *)
         let* r, s_for_body_new, so_list =
           sforloop_eq
             eq_loc genv env size for_kind for_resume for_body
             i_env s_for_body so_list in
         let s_for_body = if for_resume then s_for_body_new
                            else s_for_body in
         return (r, size_of_for_kind for_kind size,
                 s_for_body, so_list, si, si_list) in
    return (r, Slist (Sopt(s_size) :: Slist(s_for_block :: so_list) ::
                        si :: si_list))
  | EQemit(x, e_opt), s ->
     let* v, s =
       match e_opt with
       | None -> return (Value(Vpresent(Vvoid)), s)
       | Some(e) ->
          let* v, s = sexp genv env e s in
          let* v =
            let+ v = v in
            return (Value(Vpresent(v))) in
          return (v, s) in
     let* _ =
       Env.find_opt x env |>
         Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = eq_loc } in
     return (Env.singleton x { empty with cur = Some(v) }, s)
  | _ -> error { kind = Estate; loc = eq_loc }

(* how the size must be kept or not from one reaction to the other *)
and size_of_for_kind for_kind size =
  match for_kind with
  (* between steps, the size of a foreach must not change *)
  | Kforeach -> Some(Value(Vint(size)))
  (* whereas it can change for a forward loop *)
  | Kforward _ -> None

and sforloop_eq
  loc genv env size for_kind for_resume { for_out; for_block }
  i_env s_for_block so_list =
  match i_env with
  | Vbot -> return (Match.bot_env for_block.b_write, s_for_block, so_list)
  | Vnil -> return (Match.nil_env for_block.b_write, s_for_block, so_list)
  | Value(i_env) ->
     (* 1/ computes the environment from the [returns] *)
     (* environment [env_v + acc_env]. Vars in [acc_env] *)
     (* are accumulated values such that *)
     (* [acc_env(last x)(i) = acc_env(x)(i-1)] where [i] is the *)
     (* iteration index. *)
     let* acc_env, so_list =
       mapfold2 { kind = Estate; loc }
         (sfor_out genv env) Env.empty for_out so_list in
     (* 2/ runs the body *)
     let* missing, env_list, acc_env, s_for_block =
       match for_kind, s_for_block with
       | Kforeach, Slist(s_list) ->
          let sbody env acc_env s =
            sforblock genv env acc_env for_block None s in
          let* env_list, acc_env, s_list =
            Forloop.foreach_eq loc
              sbody env i_env acc_env s_list in
          return (0, env_list, acc_env, Slist(s_list))
       | Kforward(exit), _ ->
          let sbody env acc_env s =
            sforblock genv env acc_env for_block exit s in
          let* env_list, acc_env, s_for_block_new =
            Forloop.forward_eq loc
              sbody env i_env acc_env size s_for_block in
          (* was-it a complete iteration? *)
          let missing = size - List.length env_list in
          let s_for_block =
            if for_resume then s_for_block_new else s_for_block in
          return (missing, env_list, acc_env, s_for_block)
       | _ -> error { kind = Estate; loc } in
     (* store the next last value for [for_out] - only necessary *)
     (* when [resume = true] *)
     let* so_list = 
       if for_resume then
         map2 { kind = Estate; loc } (set_foreq_out acc_env) for_out so_list
       else return so_list in
     let* env =
       for_env_out missing env_list acc_env loc for_out in
     return (env, s_for_block, so_list)

(* store the next value for [last x] in the state of [for_out] *)
(* this function assumes that the forloop is resumed *)
(* the state is organised in [s_init; s_default] *)
(* take the entry [last x] in the environment because it is an accumulation *)
and set_foreq_out env_eq { desc = { for_name }; loc } s =
  let* v =
    find_last_opt for_name env_eq |>
      Opt.to_result ~none:{ kind = Eundefined_ident(for_name); loc } in
  match s with
  | Slist [Sempty; _] -> return s
  | Slist [Slist [Sopt _; s_init]; s_default] ->
     (* store the current value of [var_name] into the state *)
     return (Slist [Slist [Sopt(Some(v)); s_init]; s_default])
  | Slist [_; s_default] ->
     (* store the current value of [var_name] into the state *)
     return (Slist [Sval(v); s_default])
  | _ ->
     error { kind = Estate; loc }

(* the same - for the second form of for loops *)
and set_forexp_out env_eq { desc = { for_vardec = { var_name } }; loc } s =
   let* v =
    find_last_opt var_name env_eq |>
      Opt.to_result ~none:{ kind = Eundefined_ident(var_name); loc } in
  match s with
  | Slist [Sempty; _] -> return s
  | Slist [Slist [Sopt _; s_init]; s_default] ->
     (* store the current value of [var_name] into the state *)
     return (Slist [Slist [Sopt(Some(v)); s_init]; s_default])
  | Slist [_; s_default] ->
     (* store the current value of [var_name] into the state *)
     return (Slist [Sval(v); s_default])
  | _ ->
     error { kind = Estate; loc }

(* Evaluation of the result of a function *)
and sresult genv env { r_desc; r_loc } s =
  match r_desc with
  | Exp(e) -> sexp genv env e s
  | Returns(b) ->
     Debug.print_ienv "Return (env): before" env;
     let* env, env_visible, s = sblock genv env b s in
     Debug.print_ienv "Return (env): after" env;
     Debug.print_ienv "Return (env visible): after" env_visible;
     let* v = matching_out env b in
     return (v, s)

(* block [local x1 [init e1 | default e1 | ],..., xn [...] do eq done *)
and sblock genv env { b_vars; b_body; b_loc } s_b =
  match s_b with
  | Slist (s_eq :: s_list) ->
     let* bot_x, s_list =
       mapfold3 { kind = Estate; loc = b_loc }
         (svardec genv env) Env.empty b_vars s_list (bot_list b_vars) in
     let names = Match.names_env bot_x in
     (* double the number of iterations because a variable [x] *)
     (* can be defined by an equation [x = ...] and [init x = ...] *)
     let n = 2 * Env.cardinal bot_x + 1 in
     let* (env_eq_not_x, env_eq_x), s_eq = 
       Fix.local genv env seq b_body n s_eq bot_x in
     (* a dynamic check of causality: all locally defined names *)
     (* [x1,...,xn] must be non bottom provided that the value of *)
     (* all free variables is not bottom *)
     let* _ = Fix.causal b_loc env env_eq_x names in
     (* store the next last value for [svardec] *)
     let* s_list = map2 { kind = Estate; loc = b_loc }
                     (set_vardec env_eq_x) b_vars s_list in
     (* add local variables to [env] *)
     let env = Env.append env_eq_x (Env.append env_eq_not_x env) in
     return (env, env_eq_not_x, Slist (s_eq :: s_list))
  | _ ->
     error { kind = Estate; loc = b_loc }

(* a reset is possible for combinatorial or stateful expressions *)
and sblock_with_reset genv env b_eq s_eq r =
  let* s_eq =
    if r then
      (* recompute the initial state *)
      iblock false genv env b_eq
    else
      (* keep the current one *)
      return s_eq in
  sblock genv env b_eq s_eq

(* computes one step for the body of a for loop *)
(* for[ward|each] [resume] (n)[i](...) returns (acc_env)
     local x1,...,xm do eq [[while|until|unless] c] *)
and sforblock genv env acc_env b for_exit s_b =
  (* the semantics for a block [local x1,...,xn do eq] *)
  let sbody genv env b s_b acc_env =
    let sem s_b env_in =
      let* env, env_eq_not_x, s_b =
        sblock genv (Env.append env_in env) b s_b in
      let new_env_in = Fix.complete env_in env_eq_not_x in
      return ((env, new_env_in), s_b) in
    let* _, (env, new_acc_env), s_b =
      Fix.fixpoint b.b_loc (Env.cardinal acc_env + 1) Fix.stop sem s_b acc_env
    in
    return (env, new_acc_env, s_b) in
  (* evaluation function for the exit condition; the condition *)
  (* must be stateless. *)
  let cond env e = vexp genv env e in
  (* tell wheither a condition is true or not *)
  let exit_condition loc v =
    match v with
    | Vbot -> return false
    | Vnil -> return false
    | Value(v) ->
       let* v = Opt.to_result ~none:{ kind = Etype; loc } (is_bool v) in
       return v in
  (* main entry *)
  match for_exit with
  | None ->
     let* env, new_acc_env, s_b = sbody genv env b s_b acc_env in
     return (false, new_acc_env, s_b)
  | Some { for_exit; for_exit_kind } ->
     match for_exit_kind with
     | Ewhile ->
        let* v = cond (Env.append acc_env env) for_exit in
        let* c = exit_condition for_exit.e_loc v in
        if c then
          let* _, new_acc_env, s_b = sbody genv env b s_b acc_env in
          return (false, new_acc_env, s_b)
        else
          (* otherwise, [x = last x] for every [x] in [Dom(acc_env)] *)
          let acc_env = Forloop.lastx_to_x acc_env in
          return (true, acc_env, s_b)
     | Eunless ->
        let* v = cond (Env.append acc_env env) for_exit in
        let* c = exit_condition for_exit.e_loc v in
        if c then
          (* otherwise, [x = last x] for every [x] in [Dom(acc_env)] *)
          let acc_env = Forloop.lastx_to_x acc_env in
          return (true, acc_env, s_b)
        else
          let* _, new_acc_env, s_b = sbody genv env b s_b acc_env in
          return (false, new_acc_env, s_b)
     | Euntil ->
        let* env, new_acc_env, s_b = sbody genv env b s_b acc_env in
        let env = Env.append new_acc_env env in
        let* v = cond env for_exit in
        let* c = exit_condition for_exit.e_loc v in
        return (c, new_acc_env, s_b)

(* [v] is the returned value for [var_name] *)
and svardec genv env acc
  { var_name; var_init; var_default; var_loc; var_is_last; var_init_in_eq } s v =
  match s with
  | Slist [s_init;s_default] ->
     let* default, s_default = sexp_opt genv env var_default s_default in
     let* last, s_init =
       if var_init_in_eq then
         (* the value of [last x] is defined by the block of equations *)
         return (Some(Vbot), s_init)
       else
         match var_init, s_init with
         | None, Sval(v) ->
            if var_is_last then
              (* [x] is a state variable but it is not initialized *)
              (* this value is nil at the first instant *)
              return (Some(v), s_init)
            else error { kind = Estate; loc = var_loc }
         | _ -> sexp_init_opt var_loc genv env var_init s_init in
     let entry = { empty with cur = Some(v); last = last; default = default } in
     return (Env.add var_name entry acc, Slist [s_init; s_default])
  | _ ->
     error { kind = Estate; loc = var_loc }

(* store the next value for [last x] in the state of [vardec] declarations *)
(* the state is organised in [s_init; s_default] *)
and set_vardec env_eq { var_name; var_loc } s =
  let* v, eq =
    find_value_i_opt var_name env_eq |>
      Opt.to_result ~none:{ kind = Eundefined_ident(var_name); loc = var_loc } in
  match s with
  | Slist [Sempty; _] -> return s
  | Slist [Slist [Sopt _; s_init]; s_default] ->
     (* store the current value of [var_name] into the state *)
     (* when [eq = true], this means that the value of [last x] is *)
     (* defined by an equation [init x = ...] *)
     if eq then
       error { kind = Emerge_env { init = true; id = var_name }; loc = var_loc }
     else return (Slist [Slist [Sopt(Some(v)); s_init]; s_default])
  | Slist [_; s_default] ->
     (* store the current value of [var_name] into the state *)
     return (Slist [Sval(v); s_default])
  | _ ->
     error { kind = Estate; loc = var_loc }

(* remove entries [x, entry] from [env_eq] for *)
(* every variable [x] defined by [env_v] *)
and remove env_v env_eq =
  Env.fold (fun x _ acc -> Env.remove x acc) env_v env_eq

and sautomaton_handler_list
  loc is_weak genv env eq_write a_h_list ps pr s_list =
  (* automaton with weak transitions *)
  let rec body_and_transition_list a_h_list s_list =
    match a_h_list, s_list with
    | { s_state; s_let; s_body; s_trans; s_loc } :: a_h_list,
      (Slist [Slist(ss_let); ss_body;
               Slist(ss_trans)] as s) :: s_list ->
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
               Slist [Slist(ss_let); ss_body;
                       Slist(ss_trans)] :: s_list) in
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
      (Slist [ss_var; ss_body; Slist(ss_trans)] as s) :: s_list ->
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
             Slist [ss_var; ss_body; Slist(ss_trans)] :: s_list)
       end
    | _ -> error { kind = Estate; loc = loc } in
  (* 2/ execute the body of the target state *)
  let rec body_list a_h_list ps pr s_list =
    match a_h_list, s_list with
    | { s_state; s_let; s_body; s_loc } :: a_h_list,
      (Slist [Slist(ss_let); ss_body; ss_trans] as s) :: s_list ->
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
            (env_body, Slist [Slist(ss_let); ss_body;
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
       return (Match.bot_env eq_write, ns, nr, s_list)
    | (Vnil, _) | (_, Vnil) ->
       return (Match.bot_env eq_write, ns, nr, s_list)
    | Value(vns), Value(vnr) ->
       let* vnr =
         is_bool vnr |>
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
    Slist [s_cond; Slist(ss_let); s_body; s_next_state] :: s_list ->
     (* if [pr=true] then the transition is reset *)
     let* (v, env_cond), s_cond =
       reset (iscondpat false) sscondpat genv env e_cond s_cond pr in
     let env = Env.append env_cond env in
     let* env_body, (ns, nr), s =
       match v with
       (* if [v = bot/nil] the state and reset bit are also bot/nil *)
       | Vbot ->
          return (Match.bot_env e_body.b_write,
                  (Vbot, Vbot), Slist [s_cond; Slist(ss_let);
                                        s_body; s_next_state] :: s_list)
       | Vnil ->
          return (Match.nil_env e_body.b_write,
                  (Vnil, Vnil), Slist [s_cond; Slist(ss_let);
                                        s_body; s_next_state] :: s_list)
       | Value(v) ->
          (* revoir le traitement. L'etat des conditions *)
          (* change mais les equations ne sont evaluees que lorsque *)
          (* la condition est vraie *)
          (* le code ci-dessous ne le fait pas. *)
          let* v =
            is_bool v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
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
                  Slist [s_cond; Slist(ss_let);
                          s_body; s_next_state] :: s_list) in
     return (env_body, (ns, nr), s)
  | _ ->
     error { kind = Estate; loc = loc }

and sscondpat genv env { desc; loc } s =
  match desc, s with
  | Econdand(sc1, sc2), Slist [s1; s2] ->
     let* (v1, env_sc1), s1 = sscondpat genv env sc1 s1 in
     let* (v2, env_sc2), s2 = sscondpat genv env sc2 s2 in
     let* env_sc = merge loc env_sc1 env_sc2 in
     let s = Slist [s1; s2] in
     (match v1, v2 with
      | (Vbot, _) | (_, Vbot) -> return ((Vbot, Env.empty), s)
      | (Vnil, _) | (_, Vnil) -> return ((Vnil, Env.empty), s)
      | Value(v1), Value(v2) ->
         let* v1 =
           is_bool v1 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         let* v2 =
           is_bool v2 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         (* v1 && v2 *)
         return ((Value(Vbool(v1 && v2)), env_sc), s))
  | Econdor(sc1, sc2), Slist [s1; s2] ->
     let* (v1, env_sc1), s1 = sscondpat genv env sc1 s1 in
     let* (v2, env_sc2), s2 = sscondpat genv env sc2 s2 in
     let* env_sc = merge loc env_sc1 env_sc2 in
     (match v1, v2 with
      | (Vbot, _) | (_, Vbot) -> return ((Vbot, Env.empty), s)
      | (Vnil, _) | (_, Vnil) -> return ((Vnil, Env.empty), s)
      | Value(v1), Value(v2) ->
         let* v1 =
           is_bool v1 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         let* v2 =
           is_bool v2 |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
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
  | Econdon(sc, e), Slist [s_sc; s] ->
     let* (v, env_sc), s_sc = sscondpat genv env sc s_sc in
     let* ve, s = sexp genv env e s in
     let s = Slist [s_sc; s] in
     (match v, ve with
      | (Vbot, _) | (_, Vbot) -> return ((Vbot, env_sc), s)
      | (Vnil, _) | (_, Vnil) -> return ((Vnil, env_sc), s)
      | Value(v), Value(ve) ->
         let* v =
           is_bool v |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         let* ve =
           is_bool ve |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
         (* v on ve *)
         return ((Value(Vbool(v && ve)), env_sc), s))
  | _ -> error { kind = Estate; loc = loc }

and sstate genv env { desc; loc } s =
  match desc, s with
  | Estate0(f), Sempty -> return (Value(Vstate0(f)), Sempty)
  | Estate1(f, e_list), Slist s_list ->
     let* v_s_list =
       map2 { kind = Estate; loc = loc } (sexp genv env) e_list s_list in
     let v_list, s_list = List.split v_s_list in
     let* c =
       Primitives.state1 f v_list
       |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
     return (c, Slist(s_list))
  | Estateif(e, s1, s2), Slist [se; se1; se2] ->
     let* v, se = sexp genv env e se in
     let* s1, se1 = sstate genv env s1 se1 in
     let* s2, se2 = sstate genv env s2 se2 in
     let* v =
       Primitives.ifthenelse v s1 s2 |>
         Opt.to_result ~none:{ kind = Etype; loc = loc } in
     return (v, Slist [se; se1; se2])
  | _ -> error { kind = Estate; loc = loc }

(* application of a combinatorial function *)
and apply loc fv v_list =
  match fv, v_list with
  | _, [] -> return (Value(fv))
  | Vfun(op), v :: v_list ->
     let* v =
       Primitives.atomic v |> Opt.to_result ~none:{ kind = Etype; loc } in
     let+ v = v in
     let* fv =
       op v |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
     apply loc fv v_list
  | Vclosure { c_funexp = { f_kind; f_args; f_body } as fe;
               c_genv; c_env }, _ ->
     apply_closure loc c_genv c_env fe f_args f_body v_list
  | _ ->
     (* typing error *)
     error { kind = Etype; loc = loc }

(* apply a closure to a list of arguments *)
and apply_closure loc genv env ({ f_kind; f_loc } as fe) f_args f_body v_list =
  match f_args, v_list with
  | [], _ ->
     (* check that the kind is combinatorial *)
     let* r =
       match f_kind with
       | Knode _ ->
          error { kind = Eshould_be_combinatorial; loc }
       | Kfun _ ->
          match v_list with
          | [] -> vresult genv env f_body
          | _ -> let* fv = vresult genv env f_body in
                 let+ fv = fv in
                 apply loc fv v_list in
     return r
  | arg :: f_args, v :: v_list ->
     (* every argument is an atomic value *)
     let* v =
       Primitives.atomic v |> Opt.to_result ~none: { kind = Etype; loc } in
     let* env = Match.matching_arg_in f_loc env arg v in
     apply_closure loc genv env fe f_args f_body v_list
  | _, [] ->
     return
       (Value(Vclosure({ c_funexp = { fe with f_args = f_args };
                         c_genv = genv; c_env = env })))

(* apply a function of sizes to a list of sizes *)
and sizeapply loc fv v_list =
  (* is negative? *)
  let negative v_list = List.for_all (fun x -> x < 0) v_list in
  (* strictly less than - lexical order *)
  let lt v_list1 v_list2 =
    (* returns true if v_list1 < v_list2; lexical order of OCaml *)
    v_list1 < v_list2 in


  let apply s_params s_body s_genv s_env =
    if List.length s_params <> List.length v_list
    then error { kind = Etype; loc }
    else
      let env = 
        List.fold_left2 
          (fun acc id v -> Env.add id (Match.entry (Vint v)) acc) 
          s_env s_params v_list in
      vexp s_genv env s_body in
  match fv with
  | Vsizefun { s_params; s_body; s_genv; s_env } ->
     apply s_params s_body s_genv s_env
  | Vsizefix { bound; name; defs } ->
     let { s_params; s_body; s_genv; s_env } = Env.find name defs in
     (* when the function is recursive, the actual value of the argument *)
     (* must be strictly less than the bound and greater or equal than zero *)
     let* _ =
       match bound with
       | None -> return ()
       | Some(e_v_list) ->
         if lt v_list e_v_list && not (negative v_list) then return ()
         else
           error 
             { kind = Esize_in_a_recursive_call
                        { actual = v_list; expected = e_v_list }; loc } in
     (* the body of [name] is evaluated in its closure environment *)
     (* extended with all entries in [defs] *)
     let s_env = 
       Env.fold 
         (fun f e acc -> 
            Env.add f 
              (Match.entry 
                 (Vsizefix { bound = Some(v_list); name = f; defs })) acc)
         defs s_env in
     apply s_params s_body s_genv s_env
  | _ -> error { kind = Etype; loc }


(* evaluate an equation *)
(* check that no value is bot nor nil *)
let vleq genv env ({ l_loc } as leq) =
  let* env = vleq genv env leq in
  let* env = no_bot_no_nil_env l_loc env in
  return env

(* evaluate an expression *)
let vexp genv env ({ e_loc } as e) =
  let* v = vexp genv env e in
  no_bot_no_nil e_loc v

(* evaluate a size application *)
let sizeapply loc fv v_list =
  let* v = sizeapply loc fv v_list in
  no_bot_no_nil loc v

(* try to evaluate a boolean expression *)
and try_vexp_into_bool genv env ({ e_loc } as e) =
  let* v = vexp genv env e in
  is_bool v |> Opt.to_result ~none:{ kind = Etype; loc = e_loc }     

let implementation genv { desc; loc } =
  match desc with
  | Eopen(name) ->
     (* add [name] in the list of known modules *)
     return (Genv.open_module genv name)
  | Eletdecl { d_names; d_leq } -> 
     (* evaluate the set of equations *)
     let* env = vleq genv Env.empty d_leq in
     let* f_pvalue_list =
       map
         (fun (n, id) ->
           let* v = Env.find_opt id env |>
                      Opt.to_result ~none:{ kind = Eunbound_ident(id); loc = loc }
           in return (n, v)) d_names in
     (* debug info (a bit of imperative code here!) *)
     if !print_values then Output.letdecl Format.std_formatter f_pvalue_list;
     (* add all entries in the current global environment *)
     let genv =
       List.fold_left 
         (fun acc (f, pvalue) -> Genv.add f pvalue acc) genv f_pvalue_list in
     return genv
  | Etypedecl _ ->
     return genv

let error { kind; loc } =
  Format.eprintf "Error during evaluation\n";
  Error.message loc kind;
  raise Error

let catch v = match v with | Ok(v) -> v | Error(v) -> error v

let catch e =
  match e with
  | Ok(r) -> r
  | Error { kind; loc } ->  Error.message loc kind; raise Error

(* The main functions *)

let program genv { p_impl_list } = 
  catch (fold implementation genv p_impl_list)

(* run a unit process for [n_steps] steps *)
let eval_n n_steps init step v_list =
  let rec apply_rec s i =
    if i = n_steps then s
    else
      let r = step s v_list in
      match r with
      | Error { kind; loc } ->
         Error.message loc kind;
         Format.eprintf "@[Zrun: %d iterations out of %d.@.@]" i n_steps;
         raise Error
      | Ok(s) ->
         apply_rec s (i+1) in
  let _ = apply_rec init 0 in ()

let eval_node loc output n_steps { init; step } v  =
  let step s v =
    Debug.print_state "State before:" s;
    let* v, s = runstep loc s step v in
    Debug.print_state "State after:" s;
    output v; return s in
  eval_n n_steps init step v

let print ff (v1, v2) =
     Format.eprintf "@[The two values are not equal\n\
              first is: %a\n\
              second is: %a@]" Output.value v1 Output.value v2

let eval_two_fun loc output fv1 fv2 v_list =
  (let* v1 = apply loc fv1 v_list in
   let* v2 = apply loc fv2 v_list in
   let* v = check_equality loc v1 v2 in
   if v then return () else
     error
       { kind = Eunexpected_failure { print; arg = (v1, v2) }; loc }) |> catch

let eval_two_nodes loc output n_steps
      { init = init1; step = step1 } { init = init2; step = step2 } v =
  let step (s1, s2) v =
    Debug.print_state "State before (first node):" s1;
    let* v1, s1 = runstep loc s1 step1 v in
    Debug.print_state "State after (first node):" s1;
    Debug.print_state "State before (second node):" s2;
    let* v2, s2 = runstep loc s2 step2 v in
    Debug.print_state "State after (second node):" s2;
    let* v = check_equality loc v1 v2 in
    if v then return (s1, s2) else
      error { kind = Eunexpected_failure { print; arg = (v1, v2) }; loc } in
  eval_n n_steps (init1, init2) step v

(* Eval and print [v] *)
(* If [v] is a function with a void argument, execute its body; if [v] *)
(* is a node with a void argument, execute its body for [n] steps *)
let eval ff n_steps name v =
  match v with
  | Vclosure({ c_funexp = { f_kind; f_loc; f_args = [[]] } } as c) ->
     begin match f_kind with
     | Knode _ ->
        let si = catch (instance f_loc c) in
        Format.fprintf ff
          "@[val %s() for %d steps = @.@]" name n_steps;
        eval_node Location.no_location (Output.value_flush ff) n_steps si void
     | Kfun _ ->
        let v = catch (apply Location.no_location v [void]) in
        Format.fprintf ff
          "@[val %s() = %a@.@]" name Output.value v
     end
  | _ ->
     Format.fprintf ff "@[val %s = %a@.@]" name Output.pvalue v

(* evaluate all entries in the environment *)
let all ff n_steps { values } = E.iter (eval ff n_steps) values

(* evaluate entries in [l_names] *)
let eval_list ff n_steps genv l_names =
  let eval name =
    let v =
       find_gvalue_opt (Name name) genv |>
         Opt.to_result ~none:{ kind = Eunbound_lident(Name name);
                               loc = Location.no_location } |> catch in
    eval ff n_steps name v in
  List.iter eval l_names

(* check that all [for all n in Dom(g1), value(n) = value(g2(n))] *)
let check n_steps
      { current = { values = g1 } } { current = { values = g2 } } =
  let check name v1 v2 =
    Debug.print_message ("Checking node " ^ name);
    match v1, v2 with
    | Vclosure
      ({ c_funexp = { f_kind = k1; f_loc = loc1; f_args = [[]] } } as c1),
      Vclosure
        ({ c_funexp = { f_kind = k2; f_loc = loc2; f_args = [[]] } } as c2) ->
        begin match k1, k2 with
        | Knode _, Knode _ ->
           let si1 = catch (instance loc1 c1) in
           let si2 = catch (instance loc2 c2) in
           eval_two_nodes 
             Location.no_location Output.value_flush n_steps si1 si2 void
        | Kfun _, Kfun _ ->
           eval_two_fun Location.no_location Output.value_flush v1 v2 [void]
        | _ ->
           catch (error { kind = Etype; loc = loc1 })
        end     
    | _ -> () in
  let check name v1 =
    let v2 = E.find name g2 in
    check name v1 v2 in
  E.iter check g1
      

