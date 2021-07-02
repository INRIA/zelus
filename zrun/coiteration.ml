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
open Smisc
open Monad
open Opt                                                            
open Ident
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
           
let find_gnode_opt x env =
  let* v = Genv.find_opt x env in
  match v with
  | Gfun(f) -> return f
  | _ -> None

let find_gvalue_opt x env =
  let* v = Genv.find_opt x env in
  match v with
  | Gvalue(v) -> return v
  | _ -> None

let names env = Env.fold (fun n _ acc -> S.add n acc) env S.empty

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
    eq_write Env.empty

(* the nil environment *)
let nil_env eq_write =
  S.fold (fun x acc -> Env.add x { cur = Vnil; default = Val } acc)
    eq_write Env.empty

let size { eq_write } = S.cardinal (Deftypes.names S.empty eq_write)

(* a bot/nil value lifted to lists *)
let bot_list l = List.map (fun _ -> Vbot) l
let nil_list l = List.map (fun _ -> Vnil) l

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
(* only compare bot/nil with non bot/nil values *)
let equal_values v1 v2 =
  match v1, v2 with
  | (Vbot, Vbot) | (Vnil, Vnil) | (Value _, Value _) -> true
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
let fixpoint n equal f s bot =
  let rec fixpoint n v =
    if n <= 0 then (* this case should not happen *)
      return (0, v, s)
    else
      (* compute a fixpoint for the value [v] keeping the current state *)
      let* v', s' = f s v in
      if equal v v' then return (n, v, s') else fixpoint (n-1) v' in      
  (* computes the next state *)
  fixpoint n bot
  
let equal_env env1 env2 =
  Env.equal
    (fun { cur = cur1} { cur = cur2 } -> equal_values cur1 cur2) env1 env2
    
(* bounded fixpoint for a set of equations *)
let fixpoint_eq genv env sem eq n s_eq bot =
  let sem s_eq env_in =
    let env = Env.append env_in env in
    let* env_out, s_eq = sem genv env eq s_eq in
    let env_out = complete_with_default env env_out in
    return (env_out, s_eq) in
  print_number "Max number of iterations:" n;
  print_ienv "Fixpoint. Inital env is:" bot;
  let* m, env_out, s_eq = fixpoint n equal_env sem s_eq bot in
  print_ienv "Fixpoint. Result env is:" env_out;
  print_number "Actual number of iterations:" (n - m);
  print_number "Max was:" n;
  print_ienv "End of fixpoint with env:" env_out;
  return (env_out, s_eq)
 
(* [sem genv env e = CoF f s] such that [iexp genv env e = s] *)
(* and [sexp genv env e = f] *)
(* initial state *)
let rec iexp genv env { e_desc; e_loc } =
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
        (* [e1] must be a static expression *)
        let* v1 = Static.eval genv env e1 in
        let* s2 = iexp genv env e2 in
        let s1 =
          match v1 with | CoFun _ -> Sempty | CoNode { init } -> init in
        return (Stuple [s1; s2]) 
     | _ -> None
     end
  | Etuple(e_list) -> 
     let* s_list = Opt.map (iexp genv env) e_list in
     return (Stuple(s_list))
  | Eapp(e, e_list) ->
     let* s = iexp genv env e in
     let* s_list = Opt.map (iexp genv env) e_list in
     return (Stuple(s :: s_list))
  | Elet({ l_rec; l_eq }, e) ->
     let* s_eq = ieq genv env l_eq in
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
     let* s_handlers = Opt.map (imatch_handler_exp genv env) handlers in
     return (Stuple (se :: s_handlers))
  | Epresent { handlers; default_opt } ->
     let* s_handlers = Opt.map (ipresent_handler_exp genv env) handlers in
     let* s_default_opt = idefault genv env default_opt in
     return (Stuple (s_default_opt :: s_handlers))
  | Ereset(e_body, e_res) ->
     let* s_body = iexp genv env e_body in
     let* s_res = iexp genv env e_res in
     return (Stuple[s_body; s_res]) in
  stop_at_location e_loc r
    
and ieq genv env { eq_desc; eq_loc } =
  let r = match eq_desc with
  | EQeq(_, e) -> iexp genv env e
  | EQif(e, eq1, eq2) ->
     let* se = iexp genv env e in
     let* seq1 = ieq genv env eq1 in
     let* seq2 = ieq genv env eq2 in
     return (Stuple [se; seq1; seq2])
  | EQand(eq_list) ->
     let* seq_list = Opt.map (ieq genv env) eq_list in
     return (Stuple seq_list)
  | EQlocal(v_list, eq) ->
     let* s_v_list = Opt.map (ivardec genv env) v_list in
     let* s_eq = ieq genv env eq in
     return (Stuple [Stuple s_v_list; s_eq])
  | EQreset(eq, e) ->
     let* s_eq = ieq genv env eq in
     let* se = iexp genv env e in
     return (Stuple [s_eq; se])
  | EQautomaton(_, a_h_list) ->
     let* s_list = Opt.map (iautomaton_handler genv env) a_h_list in
     (* The initial state is the first in the list *)
     (* it is not reset at the first instant *)
     let* a_h = List.nth_opt a_h_list 0 in
     let* i = initial_state_of_automaton a_h in
     return (Stuple(Sval(Value(i)) :: Sval(Value(Vbool(false))) :: s_list))
  | EQmatch(e, m_h_list) ->
     let* se = iexp genv env e in
     let* sm_list = Opt.map (imatch_handler genv env) m_h_list in
     return (Stuple (se :: sm_list))
  | EQempty -> return Sempty
  | EQassert(e) ->
     let* se = iexp genv env e in
     return se in
  stop_at_location eq_loc r

and ivardec genv env { var_default; var_loc } =
  let r = match var_default with
  | Ewith_init(e) ->
     let* s = iexp genv env e in return (Stuple [Sopt(None); s])
  | Ewith_default(e) -> iexp genv env e
  | Ewith_nothing -> return Sempty
  | Ewith_last -> return (Sval(Vnil)) in
  stop_at_location var_loc r

and iautomaton_handler genv env { s_vars; s_body; s_trans } =
  let* sv_list = Opt.map (ivardec genv env) s_vars in
  let* sb = ieq genv env s_body in
  let* st_list = Opt.map (iescape genv env) s_trans in
  return (Stuple [Stuple(sv_list); sb; Stuple(st_list)])

(* initial state of an automaton *)
and initial_state_of_automaton { s_state = { desc } } =
  match desc with
  | Estate0pat(f) -> return (Vstate0(f))
  | _ -> None
       
and iescape genv env { e_cond; e_vars; e_body; e_next_state } =
  let* s_cond = iscondpat genv env e_cond in
  let* sv_list = Opt.map (ivardec genv env) e_vars in
  let* s_body = ieq genv env e_body in
  let* s_state = istate genv env e_next_state in
  return (Stuple [s_cond; Stuple(sv_list); s_body; s_state])

and iscondpat genv env e_cond = iexp genv env e_cond
                              
and istate genv env { desc } =
  match desc with
  | Estate0 _ -> return Sempty
  | Estate1(_, e_list) ->
     let* s_list = Opt.map (iexp genv env) e_list in
     return (Stuple(s_list))
  | Estateif(e, s1, s2) ->
     let* se = iexp genv env e in
     let* se1 = istate genv env s1 in
     let* se2 = istate genv env s2 in
     return (Stuple[se; se1; se2])

and imatch_handler genv env { m_vars; m_body } =
  let* sv_list = Opt.map (ivardec genv env) m_vars in
  let* sb = ieq genv env m_body in
  return (Stuple[Stuple(sv_list); sb])

(* pattern matching *)
(* match the value [v] against [x1,...,xn] *)
let rec matching_pateq { desc } v =
  match desc, v with
  | [x], _ -> return (Env.singleton x { cur = v; default = Val })
  | x_list, Vbot -> matching_list Env.empty x_list (bot_list x_list)
  | x_list, Vnil -> matching_list Env.empty x_list (nil_list x_list)
  | x_list, Value(Vtuple(v_list)) -> matching_list Env.empty x_list v_list
  | _ -> None

and matching_list env x_list v_list =
    match x_list, v_list with
    | [], [] ->
       return env
    | x :: x_list, v :: v_list ->
       matching_list (Env.add x { cur = v; default = Val } env) x_list v_list
    | _ -> None
         
(* match a state f(v1,...,vn) against a state name f(x1,...,xn) *)
let matching_state ps { desc } =
  match ps, desc with
  | Vstate0(f), Estate0pat(g) when Ident.compare f g = 0 -> Some Env.empty
  | Vstate1(f, v_list), Estate1pat(g, id_list) when Ident.compare f g = 0 ->
     matching_list Env.empty id_list v_list
  | _ -> None

(* match a value [ve] against a pattern [p] *)
let matching_pattern ve { desc } =
  match ve, desc with
  | Vconstr0(f), Econstr0pat(g) when Lident.compare f g = 0 -> Some(Env.empty)
  | _ -> None
       
(* [reset init step genv env body s r] resets [step genv env body] *)
(* when [r] is true *)
let reset init step genv env body s r =
  let*s = if r then init genv env body else return s in
  step genv env body s
  
(* step function *)
(* the value of an expression [e] in a global environment [genv] and local *)
(* environment [env] is a step function of type [state -> (value * state) option] *)
(* [None] is return in case of type error; [Some(v, s)] otherwise *)
let rec sexp genv env { e_desc = e_desc; e_loc } s =
  let r = match e_desc, s with   
  | Econst(v), s ->
     return (Value (value v), s)
  | Econstr0(f), s ->
     return (Value (Vconstr0(f)), s)
  | Elocal x, s ->
     let* v = find_value_opt x env in
     return (v, s)
  | Eglobal g, s ->
     let* v = find_gvalue_opt g genv in
     return (v, s)
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
        let* v_out = Initial.ifthenelse v v1 v2 in
        return (v_out, Stuple [Sval(Value(Vbool(false))); s1; s2])
     | Eifthenelse, [e1; e2; e3], Stuple [s1; s2; s3] ->
        let* v1, s1 = sexp genv env e1 s1 in
        let* v2, s2 = sexp genv env e2 s2 in
        let* v3, s3 = sexp genv env e3 s3 in
        let* v = ifthenelse v1 v2 v3 in
        return (v, Stuple [s1; s2; s3])
     | _ -> None
     end
  | Econstr1(f, e_list), Stuple(s_list) ->
     let* v_list, s_list = sexp_list genv env e_list s_list in
     (* check that all component are not nil nor bot *)
     return (strict_constr1 f v_list, Stuple(s_list))
  | Etuple(e_list), Stuple(s_list) ->
     let* v_list, s_list = sexp_list genv env e_list s_list in
     (* check that all component are not nil nor bot *)
     return (strict_tuple v_list, Stuple(s_list))
  | Eget(i, e), s ->
     let* v, s = sexp genv env e s in
     let* v = Initial.geti i v in
     return (v, s)
  | Eapp(f, e_list), Stuple (s :: s_list) ->
     let* v_list, s_list = sexp_list genv env e_list s_list in
     let* fv = find_gnode_opt f genv in
     let* v, s =
       match fv with
       | CoFun(fv) ->
          let* v_list = fv v_list in 
          let* v = tuple v_list in
          return (v, Sempty)
       | CoNode { step = fv } ->
          let* v_list, s = fv s v_list in
          let* v = tuple v_list in
          return (v, s) in
     return (v, Stuple (s :: s_list)) 
  | Elet(false, eq, e), Stuple [s_eq; s] ->
     let* env_eq, s_eq = seq genv env eq s_eq in
     let env = Env.append env_eq env in
     let* v, s = sexp genv env e s in
     return (v, Stuple [s_eq; s])
  | Elet(true, ({ eq_write } as eq), e), Stuple [s_eq; s] ->
     (* compute a bounded fix-point in [n] steps *)
     let bot = bot_env eq_write in
     let n = size eq in
     let n = if n <= 0 then 0 else n+1 in
     let* env_eq, s_eq = fixpoint_eq genv env seq eq n s_eq bot in
     (* a dynamic check of causality: all defined names in [eq] *)
     (* must be non bottom provided that all free vars. are non bottom *)
     let _ = causal env env_eq eq_write in
     let env = Env.append env_eq env in
     let* v, s = sexp genv env e s in
     return (v, Stuple [s_eq; s])
  | _ -> None in
  stop_at_location e_loc r


and sexp_list genv env e_list s_list =
  match e_list, s_list with
  | [], [] -> return ([], [])
  | e :: e_list, s :: s_list ->
     let* v, s = sexp genv env e s in
     let* v_list, s_list = sexp_list genv env e_list s_list in
     return (v :: v_list, s :: s_list)
  | _ -> None


(* step function for an equation *)
and seq genv env { eq_desc; eq_write; eq_loc } s =
  let r = match eq_desc, s with 
  | EQeq(p, e), s -> 
     let* v, s1 = sexp genv env e s in
     let* env_p1 = matching_pateq p v in
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
             let* env1 = by env env1 eq_write in
             return (env1, Stuple [se; s_eq1; s_eq2]) 
           else
             let* env2, s_eq2 = seq genv env eq2 s_eq2 in
             (* symetric completion *)
             let* env2 = by env env2 eq_write in
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
  | EQlocal(v_list, eq), Stuple [Stuple(s_list); s_eq] ->
     let* _, env_local, s_list, s_eq = sblock genv env v_list eq s_list s_eq in
     return (env_local, Stuple [Stuple(s_list); s_eq])
  | EQautomaton(is_weak, a_h_list), Stuple (Sval(ps) :: Sval(pr) :: s_list) ->
     (* [ps = state where to go; pr = whether the state must be reset or not *)
     let* env, ns, nr, s_list =
       match ps, pr with
       | (Vbot, _) | (_, Vbot) ->
          return (bot_env eq_write, ps, pr, s_list)
       | (Vnil, _) | (_, Vnil) ->
          return (nil_env eq_write, ps, pr, s_list)
       | Value(ps), Value(pr) ->
          let* pr = bool pr in
          sautomaton_handler_list
            is_weak genv env eq_write a_h_list ps pr s_list in
     return (env, Stuple (Sval(ns) :: Sval(nr) :: s_list))
  | EQmatch(e, m_h_list), Stuple (se :: s_list) ->
     let* ve, se = sexp genv env e se in
     let* env, s_list =
       match ve with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write, s_list)
       | Vnil -> return (nil_env eq_write, s_list)
       | Value(ve) ->
          smatch_handler_list genv env ve eq_write m_h_list s_list in 
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


(* block [local x1 [init e1 | default e1 | ],..., xn [...] do eq done *)
and sblock genv env v_list ({ eq_write; eq_loc } as eq) s_list s_eq =
  print_ienv "Block" env;
  let* env_v, s_list =
    Opt.mapfold3
      (svardec genv env) Env.empty v_list s_list (bot_list v_list) in
  let bot = complete env env_v eq_write in
  let n = size eq in
  let n = if n <= 0 then 0 else n+1 in
  let* env_eq, s_eq = fixpoint_eq genv env seq eq n s_eq bot in
  (* a dynamic check of causality for [x1,...,xn] *)
  let _ = causal env env_eq (names env_v) in
  (* store the next last value *)
  let* s_list = Opt.map2 (set_vardec env_eq) v_list s_list in
  (* remove all local variables from [env_eq] *)
  let env = Env.append env_eq env in
  let env_eq = remove env_v env_eq in
  let r = return (env, env_eq, s_list, s_eq) in
  stop_at_location eq_loc r

and sblock_with_reset genv env v_list eq s_list s_eq r =
  let* s_list, s_eq =
    if r then
      (* recompute the initial state *)
      let* s_list = Opt.map (ivardec genv env) v_list in
      let* s_eq = ieq genv env eq in
      return (s_list, s_eq)
    else
      (* keep the current one *)
      return (s_list, s_eq) in
  sblock genv env v_list eq s_list s_eq
  
and svardec genv env acc { var_name; var_default; var_loc } s v =
  let* default, s =
    match var_default, s with
    | Ewith_nothing, Sempty -> (* [local x in ...] *)
       return (Val, s)
    | Ewith_init(e), Stuple [si; se] ->
       let* ve, se = sexp genv env e se in
       let* lv =
         match si with
         | Sopt(None) ->
            (* first instant *)
            return (Last(ve))
         | Sval(v) | Sopt(Some(v)) -> return (Last(v))
         | _ -> None in
       return (lv, Stuple [si; se])
    | Ewith_default(e), se ->
       let* ve, se = sexp genv env e se in
       return (Default(ve), se)
    | Ewith_last, Sval(ve) -> (* [local last x in ... last x ...] *)
       return (Last(ve), s)
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
    | { s_state; s_vars; s_body; s_trans; s_loc } :: a_h_list,
      (Stuple [Stuple(ss_var_list); ss_body;
               Stuple(ss_trans)] as s) :: s_list ->
     let r = matching_state ps s_state in
     let* env_handler, ns, nr, s_list =
       match r with
       | None ->
          (* this is not the good state; try an other one *)
          let* env_handler, ns, nr, s_list =
            body_and_transition_list a_h_list s_list in
          return (env_handler, ns, nr, s :: s_list)            
       | Some(env_state) ->
          let env = Env.append env_state env in
          (* execute the body *)
          let* env, env_body, ss_var_list, ss_body =
            sblock_with_reset genv env s_vars s_body ss_var_list ss_body pr in
          (* execute the transitions *)
          let* env_trans, (ns, nr), ss_trans =
            sescape_list genv env s_trans ss_trans ps pr in
          return
            (env_body, ns, nr,
             Stuple [Stuple(ss_var_list); ss_body;
                     Stuple(ss_trans)] :: s_list) in
     (* complete missing entries in the environment *) 
     let* env_handler = by env env_handler eq_write in
     return (env_handler, ns, nr, s_list)
    | _ -> None in 
  
  (* automaton with strong transitions *)
  (* 1/ choose the active state by testing unless transitions of the *)
  (* current state *)
  let rec transition_list a_h_list s_list =
    match a_h_list, s_list with
    | { s_state; s_trans } :: a_h_list,
      (Stuple [ss_var; ss_body; Stuple(ss_trans)] as s) :: s_list ->
     let r = matching_state ps s_state in
     begin match r with
       | None ->
          (* this is not the good state; try an other one *)
          let* env_trans, ns, nr, s_list = transition_list a_h_list s_list in
          return (env_trans, ns, nr, s :: s_list)            
       | Some(env_state) ->
          let env = Env.append env_state env in
          (* execute the transitions *)
          let* env_trans, (ns, nr), ss_trans =
            sescape_list genv env s_trans ss_trans ps pr in
          return
            (env_trans, ns, nr,
             Stuple [ss_var; ss_body; Stuple(ss_trans)] :: s_list)
     end
    | _ -> None in
  (* 2/ execute the body of the target state *)
  let rec body_list a_h_list ps pr s_list =
    match a_h_list, s_list with
    | { s_state; s_vars; s_body } :: a_h_list,
      (Stuple [Stuple(ss_var_list); ss_body; ss_trans] as s) :: s_list ->
       let r = matching_state ps s_state in
       begin match r with
         | None ->
            (* this is not the good state; try an other one *)
            let* env_body, s_list = body_list a_h_list ps pr s_list in
            return (env_body, s :: s_list)            
         | Some(env_state) ->
            let env = Env.append env_state env in
            (* execute the body *)
            let* _, env_body, ss_var_list, ss_body =
              sblock_with_reset genv env s_vars s_body ss_var_list ss_body pr in
            return
              (env_body, Stuple [Stuple(ss_var_list); ss_body;
                                 ss_trans] :: s_list)
       end
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
       let* env_handler = by env env_handler eq_write in
       return (env_handler, ns, nr, s_list)

(* [Given a transition t, a name ps of a state in the automaton, a value pr *)
(* for the reset condition, *)
(* [escape_list genv env { e_cond; e_vars; e_body; e_next_state } ps pr] *)
(* returns an environment, a new state name, a new reset condition and *)
(* a new state *)
and sescape_list genv env escape_list s_list ps pr =
  match escape_list, s_list with
  | [], [] -> return (Env.empty, (Value ps, Value (Vbool false)), [])
  | { e_cond; e_reset; e_vars; e_body; e_next_state; e_loc } :: escape_list,
    Stuple [s_cond; Stuple(s_var_list); s_body; s_next_state] :: s_list ->
      (* if [pr=true] then the transition is reset *)
     let* v, s_cond = reset iscondpat sscondpat genv env e_cond s_cond pr in
     let* env_body, (ns, nr), s =
       match v with
       (* if [v = bot/nil] the state and reset bit are also bot/nil *)
       | Vbot ->
          return (bot_env e_body.eq_write,
                  (Vbot, Vbot), Stuple [s_cond; Stuple(s_var_list);
                                        s_body; s_next_state] :: s_list)
       | Vnil ->
          return (nil_env e_body.eq_write, 
                  (Vnil, Vnil), Stuple [s_cond; Stuple(s_var_list);
                                        s_body; s_next_state] :: s_list)
       | Value(v) ->
          (* revoir le traitement. L'etat des conditions *)
          (* change mais les equations ne sont evaluees que lorsque *)
          (* la condition est vraie *)
          (* le code ci-dessous ne le fait pas. *)
          let* v = bool v in
          let* env, env_body, s_var_list, s_body =
            sblock_with_reset genv env e_vars e_body s_var_list s_body pr in
          let* ns, s_next_state = sstate genv env e_next_state s_next_state in
          let* env_others, (s, r), s_list =
            sescape_list genv env escape_list s_list ps pr in
          let ns, nr = 
            if v then (ns, Value(Vbool(e_reset))) else (s, r) in
          return (env_body, (ns, nr),
                  Stuple [s_cond; Stuple(s_var_list);
                          s_body; s_next_state] :: s_list) in
     let r = return (env_body, (ns, nr), s) in
     stop_at_location e_loc r
  | _ -> None
    
and sscondpat genv env e_cond s = sexp genv env e_cond s
                              
and sstate genv env { desc; loc } s =
  match desc, s with
  | Estate0(f), Sempty -> return (Value(Vstate0(f)), Sempty)
  | Estate1(f, e_list), Stuple s_list ->
     let* v_s_list = Opt.map2 (sexp genv env) e_list s_list in
     let v_list, s_list = List.split v_s_list in
     return (Value(Vstate1(f, v_list)), Stuple(s_list))
  | _ -> None

and smatch_handler_list genv env ve eq_write m_h_list s_list =
  match m_h_list, s_list with
  | [], [] -> None
  | { m_pat; m_vars; m_body } :: m_h_list,
    (Stuple [Stuple(ss_var_list); ss_body] as s) :: s_list ->
     let r = matching_pattern ve m_pat in
     let* env_handler, s_list =
       match r with
       | None ->
          (* this is not the good handler; try an other one *)
          let* env_handler, s_list =
            smatch_handler_list genv env ve eq_write m_h_list s_list in
          return (env_handler, s :: s_list)
       | Some(env_pat) ->
          let env = Env.append env_pat env in
          let* _, env_handler, ss_var_list, ss_body =
            sblock genv env m_vars m_body ss_var_list ss_body in
          return
            (env_handler, Stuple [Stuple(ss_var_list); ss_body] :: s_list) in
     (* complete missing entries in the environment *)
     let* env_handler = by env env_handler eq_write in
     return (env_handler, s_list)
  | _ -> None

let matching_in env { var_name; var_default } v =
  return (Env.add var_name { cur = v; default = Val } env)

let matching_out env { var_name; var_default } =
  find_value_opt var_name env
  
let funexp genv { f_kind; f_atomic; f_args; f_res; f_body; f_loc } =
  let* si = ieq genv Env.empty f_body in
  let f = match f_kind with
  | Efun ->
     (* combinatorial function *)
     return
       (CoFun
          (fun v_list ->
            let* env =
              Opt.fold2 matching_in Env.empty f_args v_list in
            let* env, _ = seq genv env f_body si in
            let* v_list = Opt.map (matching_out env) f_res in
            return (v_list)))
  | Enode ->
     (* stateful function *)
     (* add the initial state for the input and output vardec *)
     let* s_f_args = Opt.map (ivardec genv Env.empty) f_args in
     let* s_f_res = Opt.map (ivardec genv Env.empty) f_res in
     return
       (CoNode
          { init = Stuple [Stuple(s_f_args); Stuple(s_f_res); si];
            step =
              fun s v_list ->
              match s with
              | Stuple [Stuple(s_f_args); Stuple(s_f_res); s_body] ->
                  (* associate the input value to the argument *) 
                 let* env_args, s_f_args =
                   Opt.mapfold3 (svardec genv Env.empty)
                     Env.empty f_args s_f_args v_list in
                 let* env_res, s_f_res =
                   Opt.mapfold3 (svardec genv env_args)
                     Env.empty f_res s_f_res (bot_list f_res) in
                 print_ienv "Node before fixpoint (args)" env_args;
                 print_ienv "Node before fixpoint (res)" env_res;
                 (* eprint_env env_args; *)
                 let n = Env.cardinal env_res in
                 let n = if n <= 0 then 0 else n+1 in
                 let* env_body, s_body =
                   fixpoint_eq genv env_args seq f_body n s_body env_res in
                 (* store the next last value *)
                 print_ienv "Node after fixpoint (body)" env_body;
                 let* s_f_res = Opt.map2 (set_vardec env_body) f_res s_f_res in
                 let* v_list = Opt.map (matching_out env_body) f_res in
                 return (v_list,
                         (Stuple [Stuple(s_f_args); Stuple(s_f_res); s_body]))
              | _ -> None }) in
  stop_at_location f_loc f

let exp genv env e =
  let* init = iexp genv env e in
  let step s = sexp genv env e s in
  return (CoF { init = init; step = step })
  
let implementation genv { desc; loc } =
  let r = match desc with
  | Eletdecl(f, e) ->
     (* [e] should be stateless, that is, [step s = v, s] *)
     let* si = iexp genv Env.empty e in
     let* v, s = sexp genv Env.empty e si in
     return (Genv.add (Name(f)) (Gvalue(v)) genv)
  | Eletfundecl(f, fd) ->
     let* fv = funexp genv fd in
     return (Genv.add (Name(f)) (Gfun(fv)) genv)
  | Etypedecl(f, td) ->
     return genv in
  stop_at_location loc r 
     
let program genv i_list = Opt.fold implementation genv i_list

(* check that a value is causally correct (non bot) *)
(* and initialized (non nil) *)
let not_bot_nil v_list =
  let not_bot_nil v =
    match v with
    | Vbot ->
       Format.eprintf "Causality error.@."; raise Stdlib.Exit
    | Vnil ->
       Format.eprintf "Initialization error.@."; raise Stdlib.Exit
    | Value(v) ->
       return v in
  Opt.map not_bot_nil v_list
    
(* run a combinatorial expression *)
(* returns the number of successful iterations *)
let run_fun output fv n =
  let rec runrec i =
    if i = n then i
    else
      let v =
        let* v_list = fv [] in
        let* v_list = not_bot_nil v_list in
        output v_list in
      if Option.is_none v then i
      else runrec (i+1) in
  runrec 0
      
(* run a stream process *)
let run_node output init step n =
  let rec runrec s i =
    if i = n then i
    else
      let v =
        let* v_list, s = step s [] in
        let* v_list = not_bot_nil v_list in
        let* _ = output v_list in
        return s in
      match v with | None -> i | Some(s) -> runrec s (i+1) in
  runrec init 0

(* The main entry function *)
let run genv main ff n =
  let* fv = find_gnode_opt (Name main) genv in
  (* the main function must be of type : unit -> t *)
  let output v_list =
    let _ = Output.pvalue_list_and_flush ff v_list in
    return () in
  match fv with
  | CoFun(fv) ->
     let _ = run_fun output fv n in
     return ()
  | CoNode { init; step } ->
     let _ = run_node output init step n in
     return ()

let check genv main n =
  let* fv = find_gnode_opt (Name main) genv in
  (* the main function must be of type : unit -> bool *)
  let output v =
    if v = [Vbool(true)] then return () else None in
  match fv with
  | CoFun(fv) ->
     let i = run_fun output fv n in
     if i < n then Format.printf "Test failed: only %i iterations.\n" i;
     return ()
  | CoNode { init; step } ->
     let i = run_node output init step n in
     if i < n then Format.printf "Test failed: only %i iterations.\n" i;
     return ()
 
