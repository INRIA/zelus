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
   Univ. in June-July 2019 and the Master MPRI - M2, Fall 2019 *)
(* The original version of this code is taken from the GitHub Zrun repo. *)
(* Zrun was done right after the COVID black out in June 2020 *)
(* This new version that include Zelus constructs during spring 2021 *)
open Smisc
open Monad
open Opt                                                            
open Ident
open Genv
open Zelus
open Value
open Primitives
open Sdebug
   
let find_value_opt x env =
  let* { cur } = Env.find_opt x env in
  return cur

let find_last_opt x env =
  let* { default } = Env.find_opt x env in
  match default with
  | Last(v) -> return v
  | _ -> None
           
let find_gvalue_opt x env =
  try
    let { Global.info } = Genv.find x env in
    return info
  with
  | Not_found -> None

let names_env env = Env.fold (fun n _ acc -> S.add n acc) env S.empty

let names eq_write = Deftypes.names S.empty eq_write

(* value of an immediate constant *)
let value v =
  match v with
  | Eint(v) -> Vint(v)
  | Ebool(b) -> Vbool(b)
  | Evoid -> Vvoid
  | Efloat(f) -> Vfloat(f)
  | Echar(c) -> Vchar(c)
  | Estring(s) -> Vstring(s)

(* evaluation functions *)

(* the bottom environment *)
let bot_env eq_write =
  S.fold (fun x acc -> Env.add x { cur = Vbot; default = Val } acc)
    (names eq_write) Env.empty

(* the nil environment *)
let nil_env eq_write =
  S.fold (fun x acc -> Env.add x { cur = Vnil; default = Val } acc)
    (names eq_write) Env.empty

(* a bot/nil value lifted to lists *)
let bot_list l = List.map (fun _ -> Vbot) l
let nil_list l = List.map (fun _ -> Vnil) l

(* a bot/nil value lifted to patterns *)
let rec distribute v acc { pat_desc } =
  match pat_desc with
  | Evarpat(x) -> Env.add x v acc
  | Etuplepat(p_list) | Econstr1pat(_, p_list) ->
     List.fold_left (distribute v) acc p_list
  | Ewildpat | Econstpat _ | Econstr0pat _ -> acc
  | Ealiaspat(p, x) -> distribute v (Env.add x v acc) p
  | Eorpat(p_left, _) -> distribute v acc p_left
  | Erecordpat(p_e_list) ->
     let distribute_record acc { arg } = distribute v acc arg in
     List.fold_left distribute_record acc p_e_list
  | Etypeconstraintpat(p, _) -> distribute v acc p
                                
let pbot p = distribute Vbot Env.empty p
let pnil p = distribute Vnil Env.empty p

(* number of variables defined by an equation *)
let size { eq_write } = S.cardinal (Deftypes.names S.empty eq_write)

(* merge two environments provided they do not overlap *)
let merge env1 env2 =
  let s = Env.to_seq env1 in
  seqfold
    (fun acc (x, entry) ->
      if Env.mem x env2 then None
      else return (Env.add x entry acc))
    env2 s
                    
(* given an environment [env], a local environment [env_handler] *)
(* an a set of written variables [write] *)
(* complete [env_handler] with entries in [env] for variables that *)
(* appear in [write] *)
(* this is used for giving the semantics of a control-structure, e.g.,: *)
(* [if e then do x = ... and y = ... else do x = ... done]. When [e = false] *)
(* the value of [y] is the default one given at the definition of [y] *)
(* for the moment, we treat the absence of a default value as a type error *)
let by env env_handler write =
  S.fold
    (fun x acc ->
      (* if [x in env] but not [x in env_handler] *)
      (* then either [x = last x] or [x = default(x)] depending *)
      (* on what is declared for [x]. *)
      let* { default } as entry = Env.find_opt x env in
      if Env.mem x env_handler then acc
      else
        match default with
        | Val -> None
        | Last(v) | Default(v) ->
           let* acc = acc in
           return (Env.add x { entry with cur = v } acc))
    write (return env_handler) 
       
(* complete [env_handler] with inputs from [write] *)
(* pre-condition: [Dom(env_handler) subseteq write] *)
let complete env env_handler write =
  S.fold
    (fun x acc ->
      match Env.find_opt x env_handler with
      | Some(entry) -> Env.add x entry acc
      | None ->
         match Env.find_opt x env with
         | Some(entry) -> Env.add x entry acc
         | None -> acc (* this case should not arrive *))
    write Env.empty
  
(* given [env] and [env_handler = [x1 \ { cur1 },..., xn \ { curn }] *)
(* returns [x1 \ { cu1; default x env },..., xn \ { curn; default x env }] *)
let complete_with_default env env_handler =
  Env.fold
    (fun x ({ cur } as entry) acc ->
      match Env.find_opt x env with
      | None -> Env.add x entry acc
      | Some { default } -> Env.add x { entry with default = default } acc)
    env_handler Env.empty

(* equality of values in the fixpoint iteration. Because of monotonicity *)
(* only compare bot/nil with non bot/nil values. *)
let equal_values_or_max v1 v2 =
  match v1, v2 with
  | (_, Value _) | (Vbot, Vbot) | (Vnil, Vnil) -> true
  | _ -> false

(* Dynamic check of causality. A set of equations is causal when all defined *)
(* variables are non bottom, provided free variables are non bottom *)
(* this a very strong constraint. In particular, it rejects the situation *)
(* of a variable that is bottom but not used. *)
(* causal(env)(env_out)(names) =
 *-               /\ (forall x in Dom(env), env(x) <> bot)
 *-               /\ (env_out, _ = fixpoint_eq genv sem eq n s_eq bot)
 *-               => (forall x in names /\ Dom(env_out), env_out(x) <> bot) *)
let causal env env_out names =
  let bot v = match v with | Vbot -> true | _ -> false in
  let bot_name n =
    let r = find_value_opt n env_out in
    match r with | None -> false | Some(v) -> bot v in
  let bot_names =
    if Env.for_all (fun _ { cur } -> not (bot cur)) env
    then S.filter bot_name names else S.empty in
  let pnames ff names = S.iter (Ident.fprint_t ff) names in
  if not !set_nocausality then
    if S.is_empty bot_names then ()
    else
      begin
        Format.eprintf "The following variables are not causal:\n\
                        %a@." pnames bot_names;
        raise Stdlib.Exit
      end

(* bounded fixpoint combinator *)
(* computes a pre fixpoint f^n(bot) <= fix(f) *)
let fixpoint n stop f s bot =
  let rec fixpoint n v =
    if n <= 0 then (* this case should not happen *)
      return (0, v, s)
    else
      (* compute a fixpoint for the value [v] keeping the current state *)
      let* v', s' = f s v in
      if stop v v' then return (n, v', s') else fixpoint (n-1) v' in      
  (* computes the next state *)
  fixpoint n bot
  
(* Invariant: values in the environment are restricted by construction *)
(* to be either bot, nil or a primitive (atomic) value, i.e., a value *)
(* which is fully defined *)
let equal_env env1 env2 =
  Env.equal
    (fun { cur = cur1} { cur = cur2 } -> equal_values_or_max cur1 cur2)
    env1 env2

let max_env env =
  Env.for_all (fun _ { cur } -> match cur with | Vbot -> false | _ -> true) env

let equal_env env1 env2 =
  (max_env env2) || (equal_env env1 env2)

(* bounded fixpoint for a set of equations *)
let fixpoint_eq genv env sem eq n s_eq bot =
  let sem s_eq env_in =
    let env = Env.append env_in env in
    let* env_out, s_eq = sem genv env eq s_eq in
    let env_out = complete_with_default env env_out in
    return (env_out, s_eq) in
  Sdebug.print_number "Max number of iterations:" n;
  Sdebug.print_ienv "Fixpoint. Inital env is:" bot;
  let* m, env_out, s_eq = fixpoint n equal_env sem s_eq bot in
  Sdebug.print_ienv "Fixpoint. Result env is:" env_out;
  Sdebug.print_number "Actual number of iterations:" (n - m);
  Sdebug.print_number "Max was:" n;
  Sdebug.print_ienv "End of fixpoint with env:" env_out;
  Smisc.incr_number_of_fixpoint_iterations (n - m);
  return (env_out, s_eq)

(* pattern matching for equations [p = e] and function application *)
(* [v] is an extended value; [p] is a pattern. *)
(* The pattern matching cannot fail unless there is a typing error *)
let rec matcheq v ({ pat_loc } as p) =
  let rec matchrec acc v { pat_desc } =
    match v, pat_desc with
    | Vtuple(v_list), Etuplepat(l_list) ->
       matcheq_list acc v_list l_list
    | Vstuple(p_list), Etuplepat(l_list) ->
       matcheq_list acc (List.map (fun v -> Value v) p_list) l_list
    | Vrecord(l_v_list), Erecordpat(l_p_list) ->
       let rec find l = function
         | [] -> None
         | { label; arg = v } :: p_v_list ->
            if l = label then return v else find l p_v_list in
       Opt.fold
         (fun acc { label; arg = p } ->
           let* v = find label l_v_list in
           matchrec acc v p) acc l_p_list
    | _, Evarpat(x) ->
       return (Env.add x { cur = Value v; default = Val } acc)
    | _, Ewildpat -> return acc
    | _, Ealiaspat(p, x) ->
       let* acc = matchrec acc v p in
       return (Env.add x { cur = Value v; default = Val } acc)
    | _ -> None in
  let r = match v with
    | Vbot ->
       let env = Env.map (fun v -> { cur = v; default = Val }) (pbot p) in
       return env
    | Vnil ->
       let env = Env.map (fun v -> { cur = v; default = Val }) (pnil p) in
       return env
    | Value(v) -> matchrec Env.empty v p in
  stop_at_location pat_loc r
              
and matcheq_list acc v_list p_list =
    match v_list, p_list with
    | [], [] -> return acc
    | v :: v_list, p :: p_list  -> matcheq_list acc v_list p_list 
    | _ -> None

(* Pattern matching of a signal *)
let matchsig ve ({ pat_loc } as p) =
  let r = match ve with
    | Vbot ->
       let env = Env.map (fun v -> { cur = v; default = Val }) (pbot p) in
       return (Vbot, env)
    | Vnil ->
       let env = Env.map (fun v -> { cur = v; default = Val }) (pnil p) in
       return (Vnil, env)
    | Value(v) ->
       match v with
       | Vabsent -> return (Value(Vbool(false)), Env.empty)
       | Vpresent(v) ->
          let* env = matcheq (Value(v)) p in
          return (Value(Vbool(true)), env)
       | _ -> None in
  stop_at_location pat_loc r
  
(* match a state f(v1,...,vn) against a state name f(x1,...,xn) *)
let matching_state ps { desc; loc } =
  let r = match ps, desc with
    | Vstate0(f), Estate0pat(g) when Ident.compare f g = 0 -> return Env.empty
    | Vstate1(f, v_list), Estate1pat(g, id_list) when
           (Ident.compare f g = 0) &&
             (List.length v_list = List.length id_list) ->
       let env =
         List.fold_left2
           (fun acc v x -> Env.add x { cur = v; default = Val }  acc)
           Env.empty v_list id_list in
       return env
    | _ -> None in
  stop_at_location loc r
  
(* [reset init step genv env body s r] resets [step genv env body] *)
(* when [r] is true *)
let reset init step genv env body s r =
  let*s = if r then init genv env body else return s in
  step genv env body s


(* Pattern matching *)
let imatch_handler ibody genv env { m_body } =
  ibody genv env m_body
  
let ipresent_handler iscondpat ibody genv env { p_cond; p_body } =
  let* sc = iscondpat genv env p_cond in
  let* sb = ibody genv env p_body in
  return (Stuple [sc; sb])

let idefault_opt ibody genv env d =
  match d with
  | Init(b) -> ibody genv env b
  | Else(b) -> ibody genv env b
  | NoDefault -> return Sempty

(* [sem genv env e = CoF f s] such that [iexp genv env e = s] *)
(* and [sexp genv env e = f] *)
(* initial state *)
let rec iexp genv env { e_desc; e_loc  } =
  let r = match e_desc with
  | Econst _ | Econstr0 _ | Elocal _ | Eglobal _ | Elast _ ->
     return Sempty
  | Econstr1 { arg_list } ->
     let* s_list = Opt.map (iexp genv env) arg_list in
     return (Stuple(s_list))
  | Eop(op, e_list) ->
     begin match op, e_list with
     | Efby, [{ e_desc = Econst(v) }; e] ->
        (* synchronous register initialized with a static value *)
        let* s = iexp genv env e  in
        return (Stuple [Sval(Value (value v)); s])
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
     | Erun _, [e1; e2] ->
        (* node instanciation. [e1] must be a static expression *)
        let static_env =
          Env.filter_map (fun _ { cur } -> pvalue cur) env in
        let* v1 = Static.exp genv static_env e1 in
        let* v1 = instance v1 in
        let* s2 = iexp genv env e2 in
        return (Stuple [Sval(Value(v1)); s2])
     | Eatomic, [e] ->
        iexp genv env e
     | Etest, [e] ->
        iexp genv env e
     | Eup, [e] ->
        let* s = iexp genv env e in
        return (Stuple [Sval(Vnil); s])
     | Eperiod, [e1;e2] ->
        let* s1 = iexp genv env e1 in
        let* s2 = iexp genv env e2 in
        return (Stuple [Sval(Value(Vint(max_int))); s1; s2])
     | _ -> None
     end
  | Etuple(e_list) -> 
     let* s_list = Opt.map (iexp genv env) e_list in
     return (Stuple(s_list))
  | Eapp(e, e_list) ->
     let* s = iexp genv env e in
     let* s_list = Opt.map (iexp genv env) e_list in
     return (Stuple(s :: s_list))
  | Elet(leq, e) ->
     let* s_eq = ileq genv env leq in
     let* se = iexp genv env e in
     return (Stuple [s_eq; se])
  | Erecord_access({ arg }) ->
     iexp genv env arg
  | Erecord(r_list) ->
     let* s_list = Opt.map (fun { arg } -> iexp genv env arg) r_list in
     return (Stuple(s_list))
  | Erecord_with(e, r_list) ->
     let* se = iexp genv env e in
     let* s_list = Opt.map (fun { arg } -> iexp genv env arg) r_list in
     return (Stuple(se :: s_list))
  | Etypeconstraint(e, _) -> iexp genv env e
  | Efun _ -> return Sempty
  | Ematch { e; handlers } ->
     let* se = iexp genv env e in
     let* s_handlers = Opt.map (imatch_handler iexp genv env) handlers in
     return (Stuple (se :: s_handlers))
  | Epresent { handlers; default_opt } ->
     let* s_handlers =
       Opt.map (ipresent_handler iscondpat iexp genv env) handlers in
     let* s_default_opt = idefault_opt iexp genv env default_opt in
     return (Stuple (s_default_opt :: s_handlers))
  | Ereset(e_body, e_res) ->
     let* s_body = iexp genv env e_body in
     let* s_res = iexp genv env e_res in
     return (Stuple[s_body; s_res]) in
  stop_at_location e_loc r
    
and ieq genv env { eq_desc; eq_loc  } =
  let r = match eq_desc with
  | EQeq(_, e) -> iexp genv env e
  | EQder _ -> None
  | EQinit(_, e) ->
     let* se = iexp genv env e in
     return (Stuple [Sopt(None); se])
  | EQemit(x, e_opt) ->
     let* s =
       match e_opt with | None -> return Sempty | Some(e) -> iexp genv env e in
     return s
  | EQif(e, eq1, eq2) ->
     let* se = iexp genv env e in
     let* seq1 = ieq genv env eq1 in
     let* seq2 = ieq genv env eq2 in
     return (Stuple [se; seq1; seq2])
  | EQand(eq_list) ->
     let* seq_list = Opt.map (ieq genv env) eq_list in
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
     let* s_list = Opt.map (ipresent_handler iscondpat ieq genv env) handlers in
     let* s_default_opt = idefault_opt ieq genv env default_opt in
     return (Stuple (s_default_opt :: s_list))
  | EQautomaton { handlers; state_opt } ->
     let* s_list = Opt.map (iautomaton_handler genv env) handlers in
     (* The initial state is the first in the list *)
     (* it is not given explicitely *)
     let* a_h = List.nth_opt handlers 0 in
     let* i, si = initial_state_of_automaton genv env a_h state_opt in
     return (Stuple(i :: Sval(Value(Vbool(false))) :: si :: s_list))
  | EQmatch { e; handlers } ->
     let* se = iexp genv env e in
     let* sm_list = Opt.map (imatch_handler ieq genv env) handlers in
     return (Stuple (se :: sm_list))
  | EQempty -> return Sempty
  | EQassert(e) ->
     let* se = iexp genv env e in
     return se in
  stop_at_location eq_loc r

and iblock genv env { b_vars; b_body; b_loc  } =
  let r =
    let* s_b_vars = Opt.map (ivardec genv env) b_vars in
    let* s_b_body = ieq genv env b_body in
    return (Stuple (s_b_body :: s_b_vars)) in
  stop_at_location b_loc r
  
and ivardec genv env { var_init; var_default; var_loc } =
  let r =
    let* s_i =
      match var_init with
      | None -> return Sempty
      | Some(e) -> let* s = iexp genv env e in return (Stuple [Sopt(None); s]) in
    let* s_d =
      match var_default with
      | None -> return Sempty
      | Some(e) -> iexp genv env e in
    return (Stuple [s_i; s_d]) in
  stop_at_location var_loc r
  
and iautomaton_handler genv env { s_let; s_body; s_trans; s_loc } =
  let r =
    let* s_list = Opt.map (ileq genv env) s_let in
    let* s_body = iblock genv env s_body in
    let* st_list = Opt.map (iescape genv env) s_trans in
    return (Stuple [Stuple(s_list); s_body; Stuple(st_list)]) in
  stop_at_location s_loc r

and ileq genv env { l_eq } = ieq genv env l_eq
  
(* initial state of an automaton *)
and initial_state_of_automaton genv env { s_state = { desc; loc } } state_opt =
  let r =
    match state_opt with
    | None ->
       (* no initial state is given. The initial state is the first *)
       (* in the list *)
       let* i = match desc with
         | Estate0pat(f) -> return (Sval(Value(Vstate0(f)))) | _ -> None in
       return (i, Sempty)
    | Some(state) ->
       let* s = istate genv env state in
       return (Sopt(None), s) in
  stop_at_location loc r
       
and iescape genv env { e_cond; e_let; e_body; e_next_state; e_loc } =
  let r =
    let* s_cond = iscondpat genv env e_cond in
    let* s_list = Opt.map (ileq genv env) e_let in
    let* s_body = iblock genv env e_body in
    let* s_state = istate genv env e_next_state in
    return (Stuple [s_cond; Stuple(s_list); s_body; s_state]) in
  stop_at_location e_loc r
    
and iscondpat genv env { desc; loc } =
  let r = match desc with
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
       return (Stuple [s_sc; se]) in
  stop_at_location loc r
                              
and istate genv env { desc; loc } =
  let r = match desc with
    | Estate0 _ -> return Sempty
    | Estate1(_, e_list) ->
       let* s_list = Opt.map (iexp genv env) e_list in
       return (Stuple(s_list))
    | Estateif(e, s1, s2) ->
       let* se = iexp genv env e in
       let* se1 = istate genv env s1 in
       let* se2 = istate genv env s2 in
       return (Stuple[se; se1; se2]) in
  stop_at_location loc r

and iresult genv env { r_desc; r_loc } =
  let r = match r_desc with
    | Exp(e) -> iexp genv env e
    | Returns(b) -> iblock genv env b in
  stop_at_location r_loc r
    

(* The main step function *)
(* the value of an expression [e] in a global environment [genv] and local *)
(* environment [env] is a step function. *)
(* Its type is [state -> (value * state) option] *)
and sexp genv env { e_desc = e_desc; e_loc } s =
  let r = match e_desc, s with   
  | Econst(v), s ->
     return (Value (value v), s)
  | Econstr0 { lname }, s ->
     return (Value (Vconstr0(lname)), s)
  | Elocal x, s ->
     let* v = find_value_opt x env in
     return (v, s)
  | Eglobal { lname }, s ->
     let* v = find_gvalue_opt lname genv in
     return (Value(v), s)
  | Elast x, s ->
     let* v = find_last_opt x env in
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
       (* see [paper EMSOFT'06] *)
        let* v1, s1 = sexp genv env e1 s1  in
        let* v2, s2 = sexp genv env e2 s2  in
        let* v_out = Primitives.ifthenelse v v1 v2 in
        return (v_out, Stuple [Sval(Value(Vbool(false))); s1; s2])
     | Eifthenelse, [e1; e2; e3], Stuple [s1; s2; s3] ->
        let* v1, s1 = sexp genv env e1 s1 in
        let* v2, s2 = sexp genv env e2 s2 in
        let* v3, s3 = sexp genv env e3 s3 in
        let* v = ifthenelse v1 v2 v3 in
        return (v, Stuple [s1; s2; s3])
     | Erun _, [_; e2], Stuple [Sval(Value(Vnode { init; step })); s2] ->
        (* the first argument [e1] is static; it does not need *)
        (* to be recomputed *)
        let* v2, s2 = sexp genv env e2 s2 in
        let* v, s = Result.to_option (step init v2) in
        return (v, Stuple [Sval(Value(Vnode { init; step })); s2])
     | Eatomic, [e], s ->
        (* if one of the input is bot (or nil), the output is bot (or nil); *)
        (* that is, [e] is considered to be strict *)
        let* v, s = sexp genv env e s in
        return (v, s)
     | Etest, [e], s ->
        let* v, s = sexp genv env e s in
        let* v = Primitives.lift1 Primitives.test v in
        return (v, s)
     | Eup, [e], Stuple [Sval(zin); _; s] ->
        (* [zin] and [zout] *)
        let* ve, s = sexp genv env e s in
        return (zin, Stuple [Sval(zin); Sval(ve); s])
     | Eperiod, [_; _], _ ->
        None
     | _ -> None
     end
  | Econstr1 { lname; arg_list }, Stuple(s_list) ->
     let* v_list, s_list = sexp_list genv env arg_list s_list in
     (* check that all component are not nil nor bot *)
     let* v = constr1 lname v_list in
     return (v, Stuple(s_list))
  | Etuple(e_list), Stuple(s_list) ->
     let* v_list, s_list = sexp_list genv env e_list s_list in
     let* v = tuple v_list in
     return (v, Stuple(s_list))
  | Eapp(e, e_list), Stuple (s :: s_list) ->
     (* [f] must return a combinatorial function *)
     let* v, s = sexp genv env e s in
     let* v_list, s_list = sexp_list genv env e_list s_list in
     let* v =
       match v with
       | Vbot -> return Vbot | Vnil -> return Vnil
       | Value(v) ->
          let* v = funvalue v in
          apply v v_list in
     return (v, Stuple (s :: s_list))
  | Elet(l_eq, e), Stuple [s_eq; s] ->
     let* env_eq, s_eq = sleq genv env l_eq s_eq in
     let env = Env.append env_eq env in
     let* v, s = sexp genv env e s in
     return (v, Stuple [s_eq; s])
  | _ -> None in
  stop_at_location e_loc r

(* application of a combinatorial function *)
and apply fv v_list =
  match v_list with
  | [] -> return (Value fv)
  | v :: v_list ->
     match fv with
     | Vfun(op) ->
        let* fv =
          match v with
          | Vbot -> return Vbot | Vnil -> return Vnil
          | Value(v) ->
             let* fv = Result.to_option (op v) in
             apply fv v_list in
        return fv
     | _ -> None
  
and sexp_list genv env e_list s_list =
  match e_list, s_list with
  | [], [] -> return ([], [])
  | e :: e_list, s :: s_list ->
     let* v, s = sexp genv env e s in
     let* v_list, s_list = sexp_list genv env e_list s_list in
     return (v :: v_list, s :: s_list)
  | _ -> None

and sleq genv env { l_rec; l_eq = ({ eq_write } as l_eq); l_loc } s_eq =
  let r =
    if l_rec then
      (* compute a bounded fix-point in [n] steps *)
      let bot = bot_env eq_write in
      let n = size l_eq in
      let n = if n <= 0 then 0 else n+1 in
      let* env_eq, s_eq = fixpoint_eq genv env seq l_eq n s_eq bot in
      (* a dynamic check of causality: all defined names in [eq] *)
      (* must be non bottom provided that all free vars. are non bottom *)
      let _ = causal env env_eq (names eq_write) in
      return (env_eq, s_eq)     
    else
      seq genv env l_eq s_eq in
  stop_at_location l_loc r
    
and slets genv env leq_list s_list =
  Opt.mapfold2 (fun acc leq s -> let* env, s = sleq genv env leq s in
                                 return (Env.append env acc, s))
    env leq_list s_list
    
(* step function for an equation *)
and seq genv env { eq_desc; eq_write; eq_loc } s =
  let r = match eq_desc, s with 
  | EQeq(p, e), s -> 
     let* v, s1 = sexp genv env e s in
     let* env_p1 = matcheq v p in
     Some (env_p1, s1) (* return (env_p, s))) *)
  | EQif(e, eq1, eq2), Stuple [se; s_eq1; s_eq2] ->
      let* v, se = sexp genv env e se in
      let* env_eq, s =
        match v with
        (* if the condition is bot/nil then all variables have value bot/nil *)
        | Vbot -> return (bot_env eq_write, Stuple [se; s_eq1; s_eq2])
        | Vnil -> return (nil_env eq_write, Stuple [se; s_eq1; s_eq2])
        | Value(b) ->
           let* v = bool b in
           if v then
             let* env1, s_eq1 = seq genv env eq1 s_eq1 in
             (* complete the output environment with default *)
             (* or last values from all variables defined in [eq_write] but *)
             (* not in [env1] *)
             let* env1 = by env env1 (names eq_write) in
             return (env1, Stuple [se; s_eq1; s_eq2]) 
           else
             let* env2, s_eq2 = seq genv env eq2 s_eq2 in
             (* symetric completion *)
             let* env2 = by env env2 (names eq_write) in
             return (env2, Stuple [se; s_eq1; s_eq2]) in
      return (env_eq, s)
  | EQand(eq_list), Stuple(s_list) ->
     let seq genv env acc eq s =
       let* env_eq, s = seq genv env eq s in
       let* acc = merge env_eq acc in
       return (acc, s) in
     let* env_eq, s_list = mapfold2 (seq genv env) Env.empty eq_list s_list in
     return (env_eq, Stuple(s_list))
  | EQreset(eq, e), Stuple [s_eq; se] -> 
     let* v, se = sexp genv env e se in 
     let* env_eq, s_eq =
       match v with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write, Stuple [s_eq; se])
       | Vnil -> return (nil_env eq_write, Stuple [s_eq; se])
       | Value(v) ->
          let* v = bool v in
          reset ieq seq genv env eq s_eq v in    
     return (env_eq, Stuple [s_eq; se])
  | EQlocal(b_eq), s_eq ->
     let* _, env_local, s_eq = sblock genv env b_eq s_eq in
     return (env_local, s_eq)
  | EQautomaton { is_weak; handlers; state_opt },
    Stuple (Sval(ps) :: Sval(pr) :: si :: s_list) ->
     (* [ps] = state where to go; *)
     (* [pr] = whether the state must be reset or not *)
     (* [si] state for [state_opt]; [s_list] state for [handlers] *)
     let* env, ns, nr, s_list =
       match ps, pr with
       | (Vbot, _) | (_, Vbot) ->
          return (bot_env eq_write, ps, pr, s_list)
       | (Vnil, _) | (_, Vnil) ->
          return (nil_env eq_write, ps, pr, s_list)
       | Value(ps), Value(pr) ->
          let* pr = bool pr in
          sautomaton_handler_list
            is_weak genv env eq_write handlers ps pr s_list in
     return (env, Stuple (Sval(ns) :: Sval(nr) :: s_list))
  | EQmatch { e; handlers }, Stuple (se :: s_list) ->
     let* ve, se = sexp genv env e se in
     let* env, s_list =
       match ve with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write, s_list)
       | Vnil -> return (nil_env eq_write, s_list)
       | Value(ve) ->
          smatch_handler_list genv env ve eq_write handlers s_list in 
     return (env, Stuple (se :: s_list))
  | EQempty, s -> return (Env.empty, s)
  | EQassert(e), s ->
     let* ve, s = sexp genv env e s in
     (* when ve is not bot/nil it must be true *)
     (* for the moment we raise a type error *)
     let* s =
       match ve with
       | Vnil | Vbot -> return s
       | Value(v) ->
          let* v = bool v in
          (* stop when [no_assert = true] *)
          if !no_assert then return s 
          else if v then return s else None in
     return (Env.empty, s)
  | _ -> None in
  stop_at_location eq_loc r

              
and sresult genv env { r_desc; r_loc } s =
  let r = match r_desc with
    | Exp(e) -> sexp genv env e s
    | Returns(b) ->
       let* env, _, s = sblock genv env b s in
       let* v = matching_arg_out env b in
       return (v, s) in
  stop_at_location r_loc r

and matching_arg_out env { b_vars; b_loc } =
  let r =
    let* v_list =
      Opt.map
        (fun { var_name } -> find_value_opt var_name env) b_vars in
    match v_list with
    | [] -> return (Value(Vvoid))
    | _ -> return (Value(Vtuple(v_list))) in
  stop_at_location b_loc r

and matching_arg_in env arg v =
  let match_in acc { var_name } v =
    return (Env.add var_name { cur = v; default = Val } acc) in
  match arg, v with
  | [], Value(Vvoid) -> return env
  | l, Value(Vtuple(v_list)) -> 
     Opt.fold2 match_in env l v_list
  | l, Value(Vstuple(v_list)) -> 
     let v_list = List.map (fun v -> Value(v)) v_list in
     Opt.fold2 match_in env l v_list
  | _ -> None
       

(* block [local x1 [init e1 | default e1 | ],..., xn [...] do eq done *)
and sblock genv env { b_vars; b_body = ({ eq_write } as eq); b_loc } s_b =
  let r = match s_b with
    | Stuple (s_eq :: s_list) ->
       Sdebug.print_ienv "Block" env;
       let* env_v, s_list =
         Opt.mapfold3 
           (svardec genv env) Env.empty b_vars s_list (bot_list b_vars) in
       let bot = complete env env_v (names eq_write) in
       let n = size eq  in
       let n = if n <= 0 then 0 else n+1 in
       let* env_eq, s_eq = fixpoint_eq genv env seq eq n s_eq bot in
       (* a dynamic check of causality for [x1,...,xn] *)
       let _ = causal env env_eq (names_env env_v) in
       (* store the next last value *)
       let* s_list = Opt.map2 (set_vardec env_eq) b_vars s_list in
       (* remove all local variables from [env_eq] *)
       let env = Env.append env_eq env in
       let env_eq = remove env_v env_eq in
       return (env, env_eq, s_eq)
    | _ -> None in
  stop_at_location b_loc r

and sblock_with_reset genv env b_eq s_eq r =
  let* s_eq =
    if r then
      (* recompute the initial state *)
      iblock genv env b_eq
    else
      (* keep the current one *)
      return s_eq in
  sblock genv env b_eq s_eq
  
and svardec genv env acc { var_name; var_default; var_init; var_loc } s v =
  (* let* default, s_default =
    match var_default, s with
    | None, Sempty -> (* [local x in ...] *)
       return (Val, s)
    | Some(e), se ->
       let* ve, se = sexp genv env e se in
       return (Default(ve), se) in *)
  let* default, s_init =
    match var_init, s with
    | None, Sempty ->
       return (Val, s)
    | Some(e), Stuple [si; se] ->
       let* ve, se = sexp genv env e se in
       let* lv =
         match si with
         | Sopt(None) ->
            (* first instant *)
            return (Last(ve))
         | Sval(v) | Sopt(Some(v)) -> return (Last(v))
         | _ -> None in
       return (lv, Stuple [si; se])
    (* | Ewith_last, Sval(ve) -> (* [local last x in ... last x ...] *)
       return (Last(ve), s) *)
    | _ -> None in
  let r = return (Env.add var_name { cur = v; default = default } acc, s) in
  stop_at_location var_loc r

(* store the next value for [last x] in the state of [vardec] declarations *)
and set_vardec env_eq { var_name; var_loc } s =
  let r = match s with
    | Sempty -> return Sempty
    | Sopt _ | Sval _ ->
       let* v = find_value_opt var_name env_eq in
       return (Sval(v))
    | Stuple [_; se] ->
       let* v = find_value_opt var_name env_eq in
       return (Stuple [Sval v; se])
    | _ -> None in
  stop_at_location var_loc r

(* remove entries [x, entry] from [env_eq] for *)
(* every variable [x] defined by [env_v] *)
and remove env_v env_eq =
  Env.fold (fun x _ acc -> Env.remove x acc) env_v env_eq

and sautomaton_handler_list is_weak genv env eq_write a_h_list ps pr s_list =
  (* automaton with weak transitions *)
  let rec body_and_transition_list a_h_list s_list =
    match a_h_list, s_list with
    | { s_state; s_let; s_body; s_trans; s_loc } :: a_h_list,
      (Stuple [Stuple(ss_let); ss_body;
               Stuple(ss_trans)] as s) :: s_list ->
       let r =
         let r = matching_state ps s_state in
         let* env_handler, ns, nr, s_list =
           match r with
           | None ->
              (* this is not the good state; try an other one *)
              let* env_handler, ns, nr, s_list =
                body_and_transition_list a_h_list s_list in
              return (env_handler, ns, nr, s :: s_list)            
           | Some(env_state) ->
              let env_state =
                Env.map
                  (fun { cur } -> { cur = Value(cur); default = Val })
                  env_state in
              let env = Env.append env_state env in
              (* execute the local lets *)
              let* env, ss_let = slets genv env s_let ss_let in
              (* execute the body *)
              let* env, env_body, ss_body =
                sblock_with_reset genv env s_body ss_body pr in
              (* execute the transitions *)
              let* env_trans, (ns, nr), ss_trans =
                sescape_list genv env s_trans ss_trans ps pr in
              return
                (env_body, ns, nr,
                 Stuple [Stuple(ss_let); ss_body;
                         Stuple(ss_trans)] :: s_list) in
         (* complete missing entries in the environment *) 
         let* env_handler = by env env_handler (names eq_write) in
         return (env_handler, ns, nr, s_list) in
       stop_at_location s_loc r
    | _ -> None in 
  
  (* automaton with strong transitions *)
  (* 1/ choose the active state by testing unless transitions of the *)
  (* current state *)
  let rec transition_list a_h_list s_list =
    match a_h_list, s_list with
    | { s_state; s_trans; s_loc } :: a_h_list,
      (Stuple [ss_var; ss_body; Stuple(ss_trans)] as s) :: s_list ->
       let r =
         let r = matching_state ps s_state in
         begin match r with
         | None ->
            (* this is not the good state; try an other one *)
            let* env_trans, ns, nr, s_list = transition_list a_h_list s_list in
            return (env_trans, ns, nr, s :: s_list)            
         | Some(env_state) ->
            let env_state =
              Env.map
                (fun { cur } -> { cur = Value(cur); default = Val })
                env_state in
            let env = Env.append env_state env in
            (* execute the transitions *)
            let* env_trans, (ns, nr), ss_trans =
              sescape_list genv env s_trans ss_trans ps pr in
            return
              (env_trans, ns, nr,
               Stuple [ss_var; ss_body; Stuple(ss_trans)] :: s_list)
         end in
       stop_at_location s_loc r
    | _ -> None in
  (* 2/ execute the body of the target state *)
  let rec body_list a_h_list ps pr s_list =
    match a_h_list, s_list with
    | { s_state; s_let; s_body; s_loc } :: a_h_list,
      (Stuple [Stuple(ss_let); ss_body; ss_trans] as s) :: s_list ->
       let r =
         let r = matching_state ps s_state in
         begin match r with
         | None ->
            (* this is not the good state; try an other one *)
            let* env_body, s_list = body_list a_h_list ps pr s_list in
            return (env_body, s :: s_list)            
         | Some(env_state) ->
            let env_state =
              Env.map
                (fun { cur } -> { cur = Value(cur); default = Val })
                env_state in
            let env = Env.append env_state env in
            (* execute the local lets *)
            let* env, ss_let = slets genv env s_let ss_let in
            (* execute the body *)
            let* _, env_body, ss_body =
              sblock_with_reset genv env s_body ss_body pr in
            return
              (env_body, Stuple [Stuple(ss_let); ss_body;
                                 ss_trans] :: s_list)
         end in
       stop_at_location s_loc r
   | _ -> None in
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
       let* vnr = bool vnr in
       let* env_body, s_list = body_list a_h_list vns vnr s_list in
       let env_handler = Env.append env_trans env_body in
       (* complete missing entries in the environment *)
       let* env_handler = by env env_handler (names eq_write) in
       return (env_handler, ns, nr, s_list)

(* [Given a transition t, a name ps of a state in the automaton, a value pr *)
(* for the reset condition, *)
(* [escape_list genv env { e_cond; e_vars; e_body; e_next_state } ps pr] *)
(* returns an environment, a new state name, a new reset condition and *)
(* a new state *)
and sescape_list genv env escape_list s_list ps pr =
  match escape_list, s_list with
  | [], [] -> return (Env.empty, (Value ps, Value (Vbool false)), [])
  | { e_cond; e_reset; e_let; e_body; e_next_state; e_loc } :: escape_list,
    Stuple [s_cond; Stuple(ss_let); s_body; s_next_state] :: s_list ->
     (* if [pr=true] then the transition is reset *)
     let r =
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
            let* v = bool v in
            (* execute the local lets *)
            let* env, ss_let = slets genv env e_let ss_let in
            let* env, env_body, s_body =
              sblock_with_reset genv env e_body s_body pr in
            let* ns, s_next_state = sstate genv env e_next_state s_next_state in
            let* env_others, (s, r), s_list =
              sescape_list genv env escape_list s_list ps pr in
            let ns, nr = 
              if v then (ns, Value(Vbool(e_reset))) else (s, r) in
            return (env_body, (ns, nr),
                    Stuple [s_cond; Stuple(ss_let);
                            s_body; s_next_state] :: s_list) in
       return (env_body, (ns, nr), s) in
     stop_at_location e_loc r
  | _ -> None
    
and sscondpat genv env { desc; loc } s = 
  let r = match desc, s with
    | Econdand(sc1, sc2), Stuple [s1; s2] ->  
       let* (v1, env_sc1), s1 = sscondpat genv env sc1 s1 in
       let* (v2, env_sc2), s2 = sscondpat genv env sc2 s2 in
       let* env = merge env_sc1 env_sc2 in
       let s = Stuple [s1; s2] in 
       (match v1, v2 with
        | (Vbot, _) | (_, Vbot) -> return ((Vbot, env), s)
        | (Vnil, _) | (_, Vnil) -> return ((Vnil, env), s)
        | Value(v1), Value(v2) ->
           let* v1 = bool v1 in
           let* v2 = bool v2 in
           (* v1 && v2 *) 
           return ((Value(Vbool(v1 && v2)), env), s))
    | Econdor(sc1, sc2), Stuple [s1; s2] ->
       let* (v1, env_sc1), s1 = sscondpat genv env sc1 s1 in
       let* (v2, env_sc2), s2 = sscondpat genv env sc2 s2 in
       let* env = merge env_sc1 env_sc2 in
       (match v1, v2 with
        | (Vbot, _) | (_, Vbot) -> return ((Vbot, env), s)
        | (Vnil, _) | (_, Vnil) -> return ((Vnil, env), s)
        | Value(v1), Value(v2) ->
           let* v1 = bool v1 in
           let* v2 = bool v2 in
           (* v1 or v2 *) 
           return ((Value(Vbool(v1 || v2)), env), s))
    | Econdexp(e_cond), s ->
       let* v, s = sexp genv env e_cond s in
       return ((v, Env.empty), s)
    | Econdpat(e, p), s ->
       let* ve, s = sexp genv env e s in
       let* ve, env_p = matchsig ve p in
       return ((ve, env_p), s)
    | Econdon(sc, e), Stuple [s_sc; s] ->
       let* (v, env_sc), s_sc = sscondpat genv env sc s_sc in
       let* ve, s = sexp genv env e s in
       let s = Stuple [s_sc; s] in
       (match v, ve with
        | (Vbot, _) | (_, Vbot) -> return ((Vbot, env_sc), s)
        | (Vnil, _) | (_, Vnil) -> return ((Vnil, env_sc), s)
        | Value(v), Value(ve) ->
           let* v = bool v in
           let* ve = bool ve in
           (* v on ve *) 
           return ((Value(Vbool(v && ve)), env), s))
    | _ -> None in
  stop_at_location loc r
                              
and sstate genv env { desc; loc } s =
  let r = match desc, s with
    | Estate0(f), Sempty -> return (Value(Vstate0(f)), Sempty)
    | Estate1(f, e_list), Stuple s_list ->
       let* v_s_list = Opt.map2 (sexp genv env) e_list s_list in
       let v_list, s_list = List.split v_s_list in
       let* v_list = Opt.map pvalue v_list in
       return (Value(Vstate1(f, v_list)), Stuple(s_list))
    | Estateif(e, s1, s2), Stuple [se; se1; se2] ->
       let* v, se = sexp genv env e se in
       let* s1, se1 = sstate genv env s1 se1 in
       let* s2, se2 = sstate genv env s2 se2 in
       let* v = ifthenelse v s1 s2 in
       return (v, Stuple [se; se1; se2])
    | _ -> None in
    stop_at_location loc r


     
and smatch_handler_list genv env ve eq_write m_h_list s_list =
  match m_h_list, s_list with
  | [], [] -> None
  | { m_pat; m_body } :: m_h_list, s :: s_list ->
     let r = Static.pmatching Env.empty ve m_pat in
     let* env_handler, s_list =
       match r with
       | None ->
          (* this is not the good handler; try an other one *)
          let* env_handler, s_list =
            smatch_handler_list genv env ve eq_write m_h_list s_list in
          return (env_handler, s :: s_list)
       | Some(env_pat) ->
          let env_pat =
            Env.map (fun v -> { cur = Value v; default = Val }) env_pat in
          let env = Env.append env_pat env in
          let* env_handler, s = seq genv env m_body s in
          return
            (env_handler, s :: s_list) in
     (* complete missing entries in the environment *)
     let* env_handler = by env env_handler (names eq_write) in
     return (env_handler, s_list)
  | _ -> None

and funexp genv env fe = Value (Vclosure(genv, env, fe))

(* Node instanciation *)
and instance v =
  match v with
  | Vnode _ -> return v
  | Vclosure({ f_kind = (Knode | Khybrid); f_args = [arg]; f_body },
             genv, env) ->
     (* compute the initial state *)
     let env = Env.map (fun v -> { cur = v; default = Val }) env in
     let* s_list = Opt.map (ivardec genv env) arg in
     let* s_body = iresult genv env f_body in
     (* compute the step function *)
     let step s v =
       to_result ~none: Error.Etype
         (let* v_list = Primitives.list_of v in
          match s with
          | Stuple (s_body :: s_list) ->
             let* env_arg, s_list =
               Opt.mapfold3 (svardec genv env) Env.empty arg s_list v_list in
             let env = Env.append env_arg env in
             let* r, s_body = sresult genv env f_body s_body in
             return (r, Stuple (s_body :: s_list))
          | _ -> None) in
     return (Vnode { init = Stuple (s_body :: s_list); step = step })
  | _ -> None 

(* Combinatorial function *)
and funvalue v =
  match v with
  | Vfun _ -> return v
  | Vclosure({ f_kind = (Kstatic | Kfun); f_args; f_body }, genv, env) ->
     let rec funrec env f_args f_body =
       match f_args with
       | [] ->
          let* ri = iresult genv env f_body in
          let* v, _ = sresult genv env f_body ri in
          let* v = pvalue v in
          return v
       | arg :: f_args ->
          return
            (Vfun
               (fun v ->
                 to_result ~none:Error.Etype
                   (let* env = matching_arg_in env arg (Value v) in
                    funrec env f_args f_body))) in
     let env = Env.map (fun v -> { cur = v; default = Val }) env in
     funrec env f_args f_body
  | _ -> None
       
    
let implementation genv { desc; loc } =
  let r = match desc with
    | Eopen(name) ->
       (* add [name] in the list of known modules *)
       return (Genv.open_module genv name)
    | Eletdecl(f, e) ->
       (* add the entry [f, v] in the current global environment *)
       let* v = Static.exp genv Env.empty e in
       return (add f v genv)
    | Etypedecl _ ->
       return genv in
  stop_at_location loc r 
     
let program genv i_list = Opt.fold implementation genv i_list
