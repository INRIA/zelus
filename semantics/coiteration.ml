(* A Denotational Semantics for Zelus *)
(* This is a companion file of working notes on the co-iterative *)
(* semantics presented at the SYNCHRON workshop, December 2019 *)
open Monad
open Opt                                                            
open Ast
open Value
open Initial

(* local and global environment *)
module Env =
  struct
    include Map.Make(Ident)

    let append env0 env =
      fold (fun x v acc -> update x (function _ -> Some(v)) acc)
        env0 env
  end
  
module Genv = Map.Make(Lident)

(* an entry in the environment *)
type 'a entry = { cur: 'a; default : 'a default }

and 'a default =
  | Val : 'a default
  | Last : 'a -> 'a default
  | Default : 'a -> 'a default

let find_value_opt x env =
  let+ { cur } = Env.find_opt x env in
  return cur

let find_last_opt x env =
  let+ { default } = Env.find_opt x env in
  match default with
  | Last(v) -> return v
  | _ -> None
           
let find_gnode_opt x env =
  let+ v = Genv.find_opt x env in
  match v with
  | Gfun(f) -> return f
  | _ -> None

let find_gvalue_opt x env =
  let+ v = Genv.find_opt x env in
  match v with
  | Gvalue(v) -> return v
  | _ -> None

(* value of an immediate constant *)
let value v =
  match v with
  | Eint(v) -> Vint(v)
  | Ebool(b) -> Vbool(b)
  | Evoid -> Vvoid
  | Efloat(f) -> Vfloat(f)
               
(* evaluation functions *)

(* the bottom environment *)
let bot_env { eq_write } =
  S.fold (fun x acc -> Env.add x { cur = Vbot; default = Val } acc)
    eq_write Env.empty

let size { eq_write } = S.fold (fun _ acc -> 1 + acc) eq_write 0
     
(* [sem genv env e = CoF f s] such that [iexp genv env e = s] *)
(* and [sexp genv env e = f] *)
(* initial state *)
let rec iexp genv env { e_desc } =
  match e_desc with
  | Econst _ | Econstr0 _ | Elocal _ | Eglobal _ | Elast _ ->
     return Sempty
  | Eop(op, e_list) ->
     begin match op, e_list with
     | Efby, [{ e_desc = Econst(v) }; e] ->
        (* synchronous register initialized with a static value *)
        let+ s = iexp genv env e  in
         return (Stuple [Sval(Value(value v)); s])
     | Efby, [e1; e2] ->
        let+ s1 = iexp genv env e1 in
        let+ s2 = iexp genv env e2 in
        return (Stuple [Sopt(None); s1; s2])
     | Eunarypre, [e] -> 
        (* un-initialized synchronous register *)
        let+ s = iexp genv env e in
        return (Stuple [Sval(Vnil); s])
     | Eifthenelse, [e1; e2; e3] ->
          let+ s1 = iexp genv env e1 in
          let+ s2 = iexp genv env e2 in
          let+ s3 = iexp genv env e3 in
          return (Stuple [s1; s2; s3])
     | _ -> None
     end
  | Etuple(e_list) -> 
     let+ s_list = Opt.map (iexp genv env) e_list in
     return (Stuple(s_list))
  | Eget(_, e) ->
     let+ s = iexp genv env e in
     return s
  | Eapp(f, e_list) ->
    let+ s_list = Opt.map (iexp genv env) e_list in
    let+ v = find_gnode_opt f genv in
    let s_list =
      match v with
      | CoFun _ -> s_list
      | CoNode { init = s } -> s :: s_list in
    return (Stuple(s_list))
  | Elet(is_rec, eq, e) ->
     let+ s_eq = ieq genv env eq in
     let+ se = iexp genv env e in
     return (Stuple [s_eq; se])
    
and ieq genv env { eq_desc } =
  match eq_desc with
  | EQeq(_, e) -> iexp genv env e
  | EQinit(_, e) -> iexp genv env e
  | EQif(e, eq1, eq2) ->
     let+ se = iexp genv env e in
     let+ seq1 = ieq genv env eq1 in
     let+ seq2 = ieq genv env eq2 in
     return (Stuple [se; seq1; seq2])
  | EQand(eq_list) ->
     let+ seq_list = Opt.map (ieq genv env) eq_list in
     return (Stuple seq_list)
  | EQlocal(v_list, eq) ->
     let+ s_v_list = Opt.map (ivardec genv env) v_list in
     let+ s_eq = ieq genv env eq in
     return (Stuple [Stuple s_v_list; s_eq])
  | EQreset(eq, e) ->
     let+ s_eq = ieq genv env eq in
     let+ se = iexp genv env e in
     return (Stuple [s_eq; se])
  | EQautomaton(_, a_h_list) ->
     let+ s_list = Opt.map (iautomaton_handler genv env) a_h_list in
     return (Stuple(s_list))
  | EQmatch(e, m_h_list) ->
     let+ se = iexp genv env e in
     let+ sm_list = Opt.map (imatch_handler genv env) m_h_list in
     return (Stuple (se :: sm_list))

and ivardec genv env { var_default } =
  match var_default with
  | Ewith_init(e) -> iexp genv env e
  | Ewith_default(e) -> iexp genv env e
  | Ewith_nothing -> return Sempty

and iautomaton_handler genv env { s_vars; s_body; s_trans } =
  let+ sv_list = Opt.map (ivardec genv env) s_vars in
  let+ sb = ieq genv env s_body in
  let+ st_list = Opt.map (iescape genv env) s_trans in
  return (Stuple [Stuple(sv_list); sb; Stuple(st_list)])

and iescape genv env { e_cond; e_vars; e_body; e_next_state } =
  let+ s_cond = iscondpat genv env e_cond in
  let+ sv_list = Opt.map (ivardec genv env) e_vars in
  let+ s_body = ieq genv env e_body in
  let+ s_state = istate genv env e_next_state in
  return (Stuple [s_cond; Stuple(sv_list); s_body; s_state])

and iscondpat genv env e_cond = iexp genv env e_cond
                              
and istate genv env { desc } =
  match desc with
  | Estate0 _ -> return Sempty
  | Estate1(_, e_list) ->
     let+ s_list = Opt.map (iexp genv env) e_list in
     return (Stuple(s_list))

and imatch_handler genv env { m_vars; m_body } =
  let+ sv_list = Opt.map (ivardec genv env) m_vars in
  let+ sb = ieq genv env m_body in
  return (Stuple[Stuple(sv_list); sb])

(* pattern matching *)
(* match the value [v] against [x1,...,xn] *)
let matching_pateq x_list v =
  let rec matching env x_list v_list =
    match x_list, v_list with
    | [], [] ->
       return env
    | x :: x_list, v :: v_list ->
       matching (Env.add x { cur = v; default = Val } env) x_list v_list
    | _ -> None in
  match v with
  | Vtuple(v_list) -> matching Env.empty x_list v_list
  | _ -> None

(* match a state f(v1,...,vn) against a state name f(x1,...,xn) *)
let matching_state ps { desc } =
  match ps, desc with
  | Sstate0(f), Estate0pat(g) when Ident.compare f g = 0 -> Some Env.empty
  | Sstate1(f, v_list), Estate1pat(g, id_list) when Ident.compare f g = 0 ->
     matching_pateq id_list (Vtuple(v_list))
  | _ -> None

(* match a value [ve] against a pattern [p] *)
let matching_pattern ve m_pat =
  match ve, m_pat with
  | Vconstr0(f), Econstr0pat(g) when Lident.compare f g = 0 -> Some(Env.empty)
  | _ -> None
       
(* bounded fixpoint combinator *)
(* computes f^n(bot) <= fix(f) *)
let fixpoint n f s bot =
  let rec fixpoint n s v =
    if n <= 0 then return (v, s)
    else
      let+ v, s = fixpoint (n-1) s v in
      f s v in
  fixpoint n s bot

(* [reset init step genv env body s r] resets [step genv env body] *)
(* when [r] is true *)
let reset init step genv env body s r =
  let+s = if r then init genv env body else return s in
  step genv env body s
  
(* step function *)
let rec sexp genv env { e_desc = e_desc } s =
  match e_desc, s with   
  | Econst(v), s ->
     return (Value(value v), s)
  | Elocal x, s ->
     let+ v = find_value_opt x env in
     return (v, s)
  | Eglobal g, s ->
     let+ v = find_gvalue_opt g genv in
     return (v, s)
  | Elast x, s ->
     let+ v = find_last_opt x env in
     return (v, s)
  | Eop(op, e_list), s ->
     begin match op, e_list, s with
     | Efby, [e1; e2], Stuple [Sval(v); s1; s2] ->
        let+ v1, s1 = sexp genv env e1 s1  in
        let+ v2, s2 = sexp genv env e2 s2  in
        return (v, Stuple [Sval(v2); s1; s2])
     | Efby, [e1; e2], Stuple [Sopt(v_opt); s1; s2] ->
        let+ v1, s1 = sexp genv env e1 s1  in
        let+ v2, s2 = sexp genv env e2 s2  in
        let v = match v_opt with | None -> v1 | Some(v) -> v in
        return (v, Stuple [Sval(v2); s1; s2])
     | Eunarypre, [e], Stuple [v; s] -> 
        let+ ve, s = sexp genv env e s in
        let+ v = match v with | Sopt(v_opt) -> v_opt | _ -> None in
        return (v, Stuple [Sval(ve); s])
     | Eifthenelse, [e1; e2; e3], Stuple [s1; s2; s3] ->
        let+ v1, s1 = sexp genv env e1 s1 in
        let+ v2, s2 = sexp genv env e2 s2 in
        let+ v3, s3 = sexp genv env e3 s3 in
        let+ v1 = basic v1 in 
        let+ v2 = basic v2 in
        let+ v3 = basic v3 in
        let+ v = ifthenelse v1 v2 v3 in
        return (Value v, Stuple [s1; s2; s3])
     | _ -> None
     end
  | Etuple(e_list), Stuple(s_list) ->
     let+ v_list, s_list = sexp_list genv env e_list s_list in
       return (Vtuple(v_list), Stuple(s_list))
  | Eget(i, e), s ->
     let+ v, s = sexp genv env e s in
     let+ v = Initial.geti i v in
     return (v, s)
  | Eapp(f, e_list), Stuple (s :: s_list) ->
     let+ v_list, s_list = sexp_list genv env e_list s_list in
     let+ fv = find_gnode_opt f genv in
     let+ v, s =
       match fv with
       | CoFun(fv) ->
          let+ v_list = fv v_list in 
          return (Vtuple(v_list), Stuple(s_list))
       | CoNode { step = fv } ->
          let+ v_list, s = fv s v_list in
          return (Vtuple(v_list), Stuple(s :: s_list)) in
     return (v, s) 
  | Elet(false, eq, e), Stuple [s_eq; s] ->
     let+ env_eq, s_eq = seq genv env eq s_eq in
     let env = Env.append env_eq env in
     let+ v, s = sexp genv env e s in
     return (v, Stuple [s_eq; s])
  | Elet(true, eq, e), Stuple [s_eq; s] ->
     (* compute a bounded fix-point with [n] steps *)
     let bot = bot_env eq in
     let n = size eq in
     let+ env_eq, s_eq =
       fixpoint n
         (fun s_eq env_eq -> seq genv (Env.append env_eq env) eq s_eq)
         s_eq bot in
     let env = Env.append env_eq env in
     let+ v, s = sexp genv env e s in
     return (v, Stuple [s_eq; s])
  | _ -> None

and sexp_list genv env e_list s_list =
  match e_list, s_list with
  | [], [] -> return ([], [])
  | e :: e_list, s :: s_list ->
     let+ v, s = sexp genv env e s in
     let+ v_list, s_list = sexp_list genv env e_list s_list in
     return (v :: v_list, s :: s_list)
  | _ -> None

(* given an environment [env], a local environment [env_w] *)
(* an a set of written variables [write] *)
(* complet [env_w] with entries in [env] for variables that appear in [write] *)
and by env env_w write =
  S.fold
    (fun x acc ->
      (* if [x in env] but not [x in env_w] *)
      (* then add a default entry in [env_w] *)
      let+ { default } as entry = Env.find_opt x env in
      if Env.mem x env_w then acc
      else
        match default with
        | Val -> None
        | Last(v) | Default(v) ->
           let+ acc = acc in
           return (Env.add x { entry with cur = v } acc))
    write (return env_w) 
                 
and seq genv env { eq_desc; eq_write } s =
  match eq_desc, s with 
  | EQeq(p, e), s -> 
     let+ v, s = sexp genv env e s in
     let+ env_p = matching_pateq p v in
     return (env_p, s)
  | EQinit(x, e), s ->
     let+ v, s = sexp genv env e s in
     return (Env.singleton x { cur = Vbot; default = Last(v) }, s)
  | EQif(e, eq1, eq2), Stuple [s; s_eq1; s_eq2] ->
      let+ v, s = sexp genv env e s in
      let+ v = basic v in
      let+ v = boolean v in
      if v then
        let+ env1, s_eq1 = seq genv env eq1 s_eq1 in
        (* complete the output environment with default *)
        (* or last values from all variables defined in [eq_write] but *)
        (* not in [env1] *)
        let+ env1 = by env env1 eq_write in
        return (env1, Stuple [s; s_eq1; s_eq2]) 
      else
        let+ env2, s_eq2 = seq genv env eq2 s_eq2 in
        (* symetric completion *)
        let+ env2 = by env env2 eq_write in
        return (env2, Stuple [s; s_eq1; s_eq2])
  | EQand(eq_list), Stuple(s_list) ->
     let+ env_eq_list, s_list = seq_list genv env eq_list s_list in
     return (env_eq_list, Stuple(s_list))
  | EQreset(eq, e), Stuple [s_eq; se] -> 
     let+ v, se = sexp genv env e se in 
     let+ v = basic v in
     let+ v = boolean v in
     let+ env_eq, s_eq = reset ieq seq genv env eq s_eq v in    
     return (env_eq, Stuple [s_eq; se])
  | EQlocal(v_list, eq), Stuple [Stuple(s_list); s_eq] ->
     let+ env, s_list, s_eq = sblock genv env v_list eq s_list s_eq in
     return (env, Stuple [Stuple(s_list); s_eq])
  | EQautomaton(is_weak, a_h_list), Stuple [ps; Sbool(pr); Stuple(s_list)] ->
      let+ env, ns, nr, s_list =
        sautomaton_handler_list
          is_weak genv env eq_write a_h_list ps pr s_list in
     return (env, Stuple [ns; Sbool(nr); Stuple(s_list)])
  | EQmatch(e, m_h_list), Stuple (se :: s_list) ->
     let+ ve, se = sexp genv env e se in
     let+ env, s_list =
       smatch_handler_list genv env ve eq_write m_h_list s_list in 
     return (env, Stuple (se :: s_list))
  | _ -> None

and sblock genv env v_list eq s_list s_eq =
  let+ env_v, s_list =
    Opt.mapfold2 (svardec genv env) Env.empty v_list s_list in
  let env = Env.append env_v env in
  let+ env_eq, s_eq =
    fixpoint 42 (fun s_eq env_eq -> seq genv (Env.append env_eq env) eq s_eq)
      s_eq Env.empty in
  (* store the next last value *)
  let+ s_list = Opt.map2 (set env_eq) v_list s_list in
  (* remove all local variables from [env_eq] *)
  let env = remove env_v env_eq in
  return (env, s_list, s_eq)

and svardec genv env env_local { var_name; var_default } s =
  let+ default, s =
    match var_default, s with
    | Ewith_nothing, Sempty -> (* [local x in ...] *)
       return (Val, s)
    | Ewith_nothing, Sopt(None) -> (* [local x in ... last x ...] *)
       (* un-initialized *)
       return (Last(Vnil), s)
    | Ewith_nothing, Sopt(Some(v)) ->
       (* initialized *)
       return (Last(v), s)
    | Ewith_init(e), Stuple [si; se] ->
       let+ ve, se = sexp genv env e se in
       let+ lv =
         match si with
         | Sopt(None) ->
            (* first instant *)
            return (Last(ve))
         | Sval(v) | Sopt(Some(v)) -> return (Last(v))
         | _ -> None in
       return (lv, Stuple [si; se])
    | Ewith_default(e), se ->
       let+ ve, se = sexp genv env e se in
       return (Default(ve), se)
    | _ -> None in
  return (Env.add var_name { cur = Vbot; default = default } env_local, s)

and set env_eq { var_name } s =
  match s with
  | Sempty -> return Sempty
  | Sopt _ | Sval _ ->
     let+ v = find_value_opt var_name env_eq in
     return (Sval(v))
  | _ -> None

(* remove entries [x, entry] from [env_eq] for *)
(* every variable [x] defined by [env_v] *)
and remove env_v env_eq =
  Env.fold (fun x _ acc -> Env.remove x acc) env_v env_eq
  
and sautomaton_handler_list is_weak genv env eq_write a_h_list ps pr s_list =
  match a_h_list, s_list with
  | { s_state; s_vars; s_body; s_trans } :: a_h_list,
    (Stuple [Stuple(ss_var_list); ss_body; Stuple(ss_trans)] as s) :: s_list ->
     let r = matching_state ps s_state in
     let+ env, ns, nr, s_list =
       match r with
       | None ->
          (* this is not the good state; try an other one *)
          let+ env, ns, nr, s_list =
            sautomaton_handler_list
              is_weak genv env eq_write a_h_list ps pr s_list in
          return (env, ns, nr, s :: s_list)            
       | Some(env_state) ->
          let env = Env.append env_state env in
          let+ env, ss_var_list, ss_body =
            sblock genv env s_vars s_body ss_var_list ss_body in
          let+ (ns, nr), ss_trans =
            sescape_list genv env s_trans ss_trans ps pr in
          return
            (env, ns, nr,
             Stuple [Stuple(ss_var_list); ss_body;
                     Stuple(ss_trans)] :: s_list) in
     return (env, ns, nr, s_list)
  | _ -> None

(* [Given a transition t, a name ps of a state in the automaton, a value pr *)
(* for the reset condition, *)
(* [escape_list genv env { e_cond; e_vars; e_body; e_next_state } ps pr] *)
(* returns a new state name, a new reset condition and a new state *)
and sescape_list genv env escape_list s_list ps pr =
  match escape_list, s_list with
  | [], [] -> return ((ps, pr), [])
  | { e_cond; e_reset; e_vars; e_body; e_next_state } :: escape_list,
    Stuple [s_cond; Stuple(s_var_list); s_body; s_next_state] :: s_list ->
      (* if [pr=true] then the transition is reset *)
     let+ v, s = reset iscondpat sscondpat genv env e_cond s_cond pr in
     let+ v = basic v in 
     let+ v = boolean v in
     let+ env_local, s_var_list, s_body =
       sblock genv env e_vars e_body s_var_list s_body in
     let env = Env.append env_local env in
     let+ ns, s_next_state = sstate genv env e_next_state s_next_state in
     let+ (s, r), s_list = sescape_list genv env escape_list s_list ps pr in
     let ns, nr =
       if v then (ns, e_reset) else (s, r) in
     return ((ns, nr),
             Stuple [s_cond; Stuple(s_var_list);
                     s_body; s_next_state] :: s_list)
  | _ -> None
    
and sscondpat genv env e_cond s = sexp genv env e_cond s
                              
and sstate genv env { desc } s =
  match desc, s with
  | Estate0(f), Sempty -> return (Sstate0(f), Sempty)
  | Estate1(f, e_list), Stuple s_list ->
     let+ v_s_list = Opt.map2 (sexp genv env) e_list s_list in
     let v_list, s_list = List.split v_s_list in
     return (Sstate1(f, v_list), Stuple(s_list))
  | _ -> None

and smatch_handler_list genv env ve eq_write m_h_list s_list =
  match m_h_list, s_list with
  | [], [] -> None
  | { m_pat; m_vars; m_body } :: m_h_list,
    (Stuple [Stuple(ss_var_list); ss_body] as s) :: s_list ->
     let r = matching_pattern ve m_pat in
     let+ env, s_list =
       match r with
       | None ->
          (* this is not the good handler; try an other one *)
          let+ env, s_list =
            smatch_handler_list genv env ve eq_write m_h_list s_list in
          return (env, s :: s_list)
       | Some(env_pat) ->
          let env = Env.append env_pat env in
          let+ env, ss_var_list, ss_body =
            sblock genv env m_vars m_body ss_var_list ss_body in
          return (env, Stuple [Stuple(ss_var_list); ss_body] :: s_list) in
     return (env, s_list)
  | _ -> None

and seq_list genv env eq_list s_list =
  let rec seq_list env_acc eq_list s_list =
    match eq_list, s_list with
    | [], [] -> return (env_acc, [])
    | eq :: eq_list, s :: s_list ->
       let+ env_eq, s = seq genv env eq s in
       let+ env_acc, s_list =
         seq_list (Env.append env_eq env_acc) eq_list s_list in
       return (env_acc, s :: s_list)
    | _ -> None in
  seq_list Env.empty eq_list s_list

let matching_in env { var_name; var_default } v =
  return (Env.add var_name { cur = v; default = Val } env)

let matching_out env { var_name; var_default } =
  find_value_opt var_name env

let funexp genv { f_kind; f_atomic; f_args; f_res; f_body } =
  let+ env =
    Opt.fold2 matching_in Env.empty f_args
      (List.map (fun _ -> Vbot) f_args) in
  let+ si = ieq genv env f_body in
  let f = match f_kind with
  | Efun ->
     (* combinatorial function *)
     CoFun
       (fun v_list ->
         let+ env =
           Opt.fold2 matching_in Env.empty f_args v_list in
         let+ env, _ = seq genv env f_body si in
         let+ v_list = Opt.map (matching_out env) f_res in
         return (v_list))
  | Enode ->
     (* stateful function *)
     CoNode
       { init = si;
         step =
           fun s v_list ->
           let+ env =
             Opt.fold2 matching_in Env.empty f_args v_list in
           let+ env, s = seq genv env f_body s in
           let+ v_list = Opt.map (matching_out env) f_res in
           return (v_list, s) } in
  return f
     
let implementation genv i =
    match i with
    | Eletdef(f, e) ->
       (* [e] should be stateless, that is, [step s = v, s] *)
       let+ si = iexp genv Env.empty e in
       let+ v, s = sexp genv Env.empty e si in
       return (Genv.add (Name(f)) (Gvalue(v)) genv)
    | Eletfun(f, fd) ->
       let+ fv = funexp genv fd in
       return (Genv.add (Name(f)) (Gfun(fv)) genv)

let program genv i_list = Opt.fold implementation genv i_list
