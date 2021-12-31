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

(* Evaluation of combinatorial expressions. The input environment *)
(* is only made of primitive values *)
(* The presence of a stateful construct leads to an error *)
open Smisc
open Monad
open Opt                                                            
open Ident
open Zelus
open Value
open Primitives
open Sdebug

let find_value_opt x env =
  let* v = Env.find_opt x env in
  match v with
  | Vbot | Vnil -> none
  | Value(v) -> return v
      
let find_gvalue_opt x env =
  try
    let { Global.info } = Genv.find x env in
    return info
  with
  | Not_found -> none

(* merge two environments provided they do not overlap *)
let merge env1 env2 =
  let s = Env.to_seq env1 in
  seqfold
    (fun acc (x, entry) ->
      if Env.mem x env2 then none
      else return (Env.add x entry acc))
    env2 s


(* value of an immediate constant *)
let immediate v =
  match v with
  | Eint(v) -> Vint(v)
  | Ebool(b) -> Vbool(b)
  | Evoid -> Vvoid
  | Efloat(f) -> Vfloat(f)
  | Echar(c) -> Vchar(c)
  | Estring(s) -> Vstring(s)
                
(* evaluation function *)
let rec exp genv env { e_desc; e_loc } =
  let r = match e_desc with   
    | Econst(v) ->
       return (immediate v)
    | Econstr0 { lname } ->
       return (Vconstr0(lname))
    | Elocal x ->
       let* v =
         find_value_opt x env |>
           Error.error e_loc (Error.Eunbound_ident(x)) in
       return v
    | Eglobal { lname } ->
       let* v =
         find_gvalue_opt lname genv |>
           Error.error e_loc (Error.Eunbound_lident(lname)) in
       return v
    | Eop(op, e_list) ->
       begin match op, e_list with
       | Eifthenelse, [e1; e2; e3] ->
          let* v = exp genv env e1 in
          let* v = bool v in
          if v then exp genv env e2
          else exp genv env e3
       | _ -> none
       end
    | Econstr1 { lname; arg_list } ->
       let* v_list = exp_list genv env arg_list in
       return (Vconstr1(lname, v_list))
    | Etuple(e_list) ->
       let* v_list = exp_list genv env e_list in
       return (Vstuple(v_list))
    | Eapp(f, e_list) ->
       let* v = exp genv env f in
       apply genv env v e_list
    | Elet({ l_rec; l_eq }, e) ->
       if l_rec then none
       else
         let* l_env = eval_eq genv env l_eq in
         exp genv (Env.append l_env env) e
    | Ematch { e; handlers } ->
       let* v = exp genv env e in
       match_handlers genv env v handlers
    | Erecord_access { label; arg } ->
       let* arg = exp genv env arg in
       record_access { label; arg }  
    | Erecord(r_list) ->
       let* r_list =
         Opt.map
           (fun { label; arg } ->
             let* arg = exp genv env arg in return ({ label; arg }))
           r_list in
       return (Vrecord(r_list))
    | Erecord_with(r, r_list) ->
       let* r = exp genv env r in
       let* label_arg_list = get_record r in
       let* ext_label_arg_list =
         Opt.map
           (fun { label; arg } ->
             let* arg = exp genv env arg in return ({ label; arg }))
           r_list in
       let* r = record_with label_arg_list ext_label_arg_list in
       return (Vrecord(r))
    | Etypeconstraint(e, _) -> exp genv env e
    | Efun(fe) ->
       funexp genv env fe
    | Epresent _ -> none
    | Ereset(e_body, e_res) ->
       let* v = exp genv env e_res in
       let* _ = bool v in
       exp genv env e_body
    | Elast _ -> none
    | Eassert(e_body) ->
       let* v = exp genv env e_body in
       let* v = bool v in
       (* stop when [no_assert = true] *)
       if !no_assert then return (Vvoid)
       else if v then return (Vvoid) else none in
  Error.stop_at_location e_loc r

and exp_list genv env e_list = Opt.map (exp genv env) e_list

and record_access { label; arg } =
  (* look for [label] in the value of [arg] *)
  let* record_list = get_record arg in
  let rec find l record_list =
    match record_list with
    | [] -> none
    | { label; arg } :: record_list ->
       if label = l then return arg
       else find l record_list in
  find label record_list
  
and record_with label_arg_list ext_label_arg_list = 
  (* inject {label; arg} into a record *)
  let rec inject label_arg_list l arg =
    match label_arg_list with
    | [] -> none
    | { label } as entry :: label_arg_list ->
       if label = l then return ({ label; arg } :: label_arg_list)
       else let* label_arg_list = inject label_arg_list l arg in
            return (entry :: label_arg_list) in
  (* join the two *)
  let rec join label_arg_list ext_label_arg_list =
    match ext_label_arg_list with
    | [] -> return label_arg_list
    | { label; arg } :: ext_label_arg_list ->
       let* label_arg_list = inject label_arg_list label arg in
       join label_arg_list ext_label_arg_list in
  join label_arg_list ext_label_arg_list
  
(* application [fv e_list] *)
and apply genv env fv e_list =
  (* apply a closure to a list of arguments *)
  let rec apply_closure genv env fe f_args e_list f_body =
    match f_args, e_list with
    | [], [] ->
       result genv env f_body
    | arg :: f_args, ({ e_loc } as e) :: e_list ->
       let* v = exp genv env e in
       let* env =
         matching_arg_in env arg v |>
           Error.error e_loc Error.Epattern_matching_failure in
       apply_closure genv env fe f_args e_list f_body
    | [], _ ->
       let* fv = result genv env f_body in
       apply genv env fv e_list
    | _, [] ->
       return (Vclosure({ fe with f_args = f_args }, genv, env)) in
  (* main entry *)
  match fv with
  | Vfun(op) ->
     let* fv =
       match e_list with
       | [] -> (* typing error *) none
       | e :: e_list ->
          let* v = exp genv env e in
          let* fv = op v in apply genv env fv e_list in
     return fv
  | Vclosure(({ f_kind = (Kstatic | Kfun);
                f_args; f_body } as fe, genv, env)) ->
     apply_closure genv env fe f_args e_list f_body
  | _ ->
     return fv
      
(* step function for an equation *)
and eval_eq genv env { eq_desc; eq_loc } =
  let r = match eq_desc with 
    | EQeq(p, e) -> 
       let* v = exp genv env e in
       let* env_p1 =
         Match.pmatcheq v p |>
           Error.error eq_loc Error.Epattern_matching_failure in
       let env_p1 = Env.map (fun v -> Value(v)) env_p1 in
       return env_p1
    | EQif(e, eq1, eq2) ->
       let* v = exp genv env e in
       let* v = bool v in
       if v then
         let* env1 = eval_eq genv env eq1 in
         return env1
       else
         let* env2 = eval_eq genv env eq2 in
         return env2
    | EQand(eq_list) ->
       let and_eq env acc eq =
         let* env_eq = eval_eq genv env eq in
         let* acc = merge env_eq acc in
         return acc in
       let* env_eq = fold (and_eq env) Env.empty eq_list in
       return env_eq
    | EQreset(eq, e) -> 
       let* v = exp genv env e in 
       let* _ = bool v in
       eval_eq genv env eq
    | EQempty -> return Env.empty
    | EQassert(e) ->
       let* v = exp genv env e in
       let* v = bool v in
       (* stop when [no_assert = true] *)
       if !no_assert then return Env.empty
       else if v then return Env.empty else none
    | EQlet({ l_rec; l_eq }, eq_let) ->
       if l_rec then none
       else
         let* l_env = eval_eq genv env l_eq in
         eval_eq genv (Env.append l_env env) eq_let
    | EQder _ | EQpresent _ | EQinit _
      | EQemit _ | EQlocal _ | EQautomaton _ | EQmatch _ -> none in
  Error.stop_at_location eq_loc r
  
and match_handlers genv env v handlers =
  match handlers with
  | [] -> none
  | { m_pat; m_body } :: handlers ->
     let r = Match.pmatch v m_pat in
     match r with
     | None ->
        (* this is not the good handler; try an other one *)
        match_handlers genv env v handlers
     | Some(env_pat) ->
        let env_pat = Env.map (fun v -> Value(v)) env_pat in
        let env = Env.append env_pat env in
        exp genv env m_body
        
and funexp genv env fe = return (Vclosure(fe, genv, env))

and block genv env { b_vars; b_body; b_loc } =
  (* a very simple solution. no fixpoint *)
  let r =
    let* _ =
      Opt.fold
        (fun acc { var_name; var_default; var_init } ->
          match var_default, var_init with
          | (None, None) -> return (S.add var_name acc)
          | _ -> none (* type error *)) S.empty b_vars in
    let* b_env = eval_eq genv env b_body in
    return (Env.append b_env env, b_env) in
  Error.stop_at_location b_loc r

and result genv env { r_desc; r_loc } =
  let r = match r_desc with
    | Exp(e) -> exp genv env e
    | Returns(b) ->
       let* env, _ = block genv env b in
       let* v = matching_arg_out env b in
       return v in
  Error.stop_at_location r_loc r

and matching_arg_out env { b_vars; b_loc } =
  let r =
    let* v_list =
      Opt.map
        (fun { var_name } -> find_value_opt var_name env) b_vars in
    match v_list with
    | [] -> return (Vvoid)
    | [v] -> return v
    | _ -> return (Vstuple(v_list)) in
  Error.stop_at_location b_loc r
  
and matching_arg_in env arg v =
  let match_in acc { var_name } v =
    return (Env.add var_name (Value(v)) acc) in
  match arg, v with
  | [], Vvoid -> return env
  | l, Vstuple(v_list) -> 
     Opt.fold2 match_in env l v_list
  | [x], _ -> match_in Env.empty x v
  | _ -> none

           
