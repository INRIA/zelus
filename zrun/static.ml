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

(* Evaluation of static expression *)
open Smisc
open Monad
open Opt                                                            
open Ident
open Zelus
open Value
open Primitives
open Sdebug

let find_value_opt x env = Env.find_opt x env
let find_gvalue_opt x env = Genv.find_opt x env

(* merge two environments provided they do not overlap *)
let merge env1 env2 =
  let s = Env.to_seq env1 in
  seqfold
    (fun acc (x, entry) ->
      if Env.mem x env2 then None
      else return (Env.add x entry acc))
    env2 s

(* match a value [ve] against a pattern [p] *)
let rec matching_pattern acc v { pat_desc } =
  match v, pat_desc with
  | _, Etypeconstraintpat(p, _) -> matching_pattern acc v p
  | (Vstate0 _| Vstate1 _ | Vclosure _), Evarpat(x) ->
     return (Env.add x v acc)
  | _, Ewildpat -> return acc
  | _, Ealiaspat(p, x) ->
     let* acc = matching_pattern acc v p in
     return (Env.add x v acc)
  | _, Eorpat(p1, p2) ->
     let env = matching_pattern Env.empty v p1 in
     let acc =
       match env with
       | None -> matching_pattern acc v p2
       | Some(env) -> return (Env.append env acc) in
     acc
  | Vrecord(l_v_list), Erecordpat(l_p_list) ->
     let matching_record acc
           { arg = v; label = l } { arg = p; label = l' } =
       if l = l' then matching_pattern acc v p
       else None in
     let compare { label = l1 } { label = l2 } = Lident.compare l1 l2 in
     let l_v_list =
       List.sort compare l_v_list in
     let l_p_list =
       List.sort compare l_p_list in
     Opt.fold2 matching_record acc l_v_list l_p_list
  | Vint(v1), Econstpat(Eint(v2)) when v1 = v2 -> return Env.empty
  | Vbool(v1), Econstpat(Ebool(v2)) when v1 = v2 -> return Env.empty
  | Vfloat(v1), Econstpat(Efloat(v2)) when v1 = v2 -> return Env.empty
  | Vchar(v1), Econstpat(Echar(v2)) when v1 = v2 -> return Env.empty
  | Vstring(v1), Econstpat(Estring(v2)) when v1 = v2 -> return Env.empty
  | Vvoid, Econstpat(Evoid) -> return Env.empty
  | Vconstr0(f), Econstr0pat(g) when Lident.compare f g = 0 ->
     return Env.empty
  | Vtuple(v_list), Etuplepat(p_list) ->
     let* v_list = Opt.map get_value v_list in
     matching_pattern_list acc v_list p_list
  | Vstuple(v_list), Etuplepat(p_list) ->
     matching_pattern_list acc v_list p_list
  | Vconstr1(f, v_list), Econstr1pat(g, p_list) when Lident.compare f g = 0 ->
     let* v_list = Opt.map get_value v_list in
     matching_pattern_list acc v_list p_list
  | Vsconstr1(f, v_list), Econstr1pat(g, p_list) when Lident.compare f g = 0 ->
     matching_pattern_list acc v_list p_list
  | _ -> None

and matching_pattern_list acc v_list p_list =
  Opt.fold2 matching_pattern acc v_list p_list
  
(* value of an immediate constant *)
let immediate v =
  match v with
  | Eint(v) -> Vint(v)
  | Ebool(b) -> Vbool(b)
  | Evoid -> Vvoid
  | Efloat(f) -> Vfloat(f)
  | Echar(c) -> Vchar(c)
  | Estring(s) -> Vstring(s)

(* evaluation functions *)
let eval genv env eval_fun e =
  let rec eval env { e_desc; e_loc } =
    let r = match e_desc with   
      | Econst(v) ->
         return (immediate v)
      | Econstr0 { lname } ->
         return (Vconstr0(lname))
      | Elocal x ->
         let* v = find_value_opt x env in
         return v
      | Eglobal { lname } ->
         let* v = find_gvalue_opt lname genv in
         return v
      | Eop(op, e_list) ->
         begin match op, e_list with
         | Eifthenelse, [e1; e2; e3] ->
            let* v = eval env e1 in
            let* v = bool v in
            if v then eval env e2
            else eval env e3
         | _ -> None 
         end
      | Econstr1 { lname; arg_list } ->
         let* v_list = eval_list env arg_list in
         return (Vsconstr1(lname, v_list))
      | Etuple(e_list) ->
         let* v_list = eval_list env e_list in
         return (Vstuple(v_list))
      | Eapp(f, e_list) ->
         let* v = eval env f in
         let* v_list = eval_list env e_list in
         let* { f_args; f_body }, env = get_closure v in
         apply env f_args v_list f_body
      | Elet({ l_rec; l_eq }, e) ->
         if l_rec then None
         else
           let* l_env = eval_eq env l_eq in
           eval (Env.append l_env env) e
      | Ematch { e; handlers } ->
         let* v = eval env e in
         match_handlers env v handlers
      | Erecord_access { label; arg } ->
     let* arg = eval env arg in
     record_access { label; arg }  
      | Erecord(r_list) ->
         let* r_list =
           Opt.map
             (fun { label; arg } ->
               let* arg = eval env arg in return ({ label; arg }))
             r_list in
         return (Vrecord(r_list))
      | Erecord_with(r, r_list) ->
         let* r = eval env r in
         let* label_arg_list = get_record r in
         let* label_arg_list' =
           Opt.map
             (fun { label; arg } ->
               let* arg = eval env arg in return ({ label; arg }))
             r_list in
         let* r = record_with label_arg_list label_arg_list in
         return (Vrecord(r))
      | Etypeconstraint(e, _) -> eval env e
      | Efun(fe) -> eval_fun genv env fe
      | Epresent _ -> None
      | Ereset(e_body, e_res) ->
         let* v = eval env e_res in
         let* _ = bool v in
         eval env e_body
      | Elast _ -> None in
    r
    
  and record_access { label; arg } =
    (* look for [label] in the value of [arg] *)
    let* record_list = get_record arg in
    let rec find l record_list =
      match record_list with
      | [] -> None
      | { label; arg } :: record_list -> if label = l then return arg
                                         else find l record_list in
    find label record_list
    
  and record_with label_arg_list ext_label_arg_list = 
    (* inject {label; arg} into a record *)
    let rec inject label_arg_list l arg =
      match label_arg_list with
      | [] -> None
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
    
  and apply env f_args v_list f_body =
    let one acc { var_name; var_default; var_init } v =
      match var_default with
      | Some _ -> None
      | None ->
         match var_init with
         | Some _ -> None
         | None ->
            return (Env.add var_name v acc) in
    let arg acc a v =
      match a, v with
      | [], Vvoid -> return acc
      | arg_list, Vtuple(v_list) ->
         let* v_list = Opt.map get_value v_list in
         Opt.fold2 one acc arg_list v_list
      | arg_list, Vstuple(v_list) ->
         Opt.fold2 one acc arg_list v_list
      | _ -> None in
    let* env = Opt.fold2 arg env f_args v_list in
    result env f_body
    
  and result env { r_desc } =
    match r_desc with
    | Exp(e) -> eval env e
    | Returns _ -> None
                 
  and eval_list env e_list =
    match e_list with
    | [] -> return []
    | e :: e_list ->
       let* v = eval env e in
       let* v_list = eval_list env e_list in
       return (v :: v_list)
       
  (* step function for an equation *)
  and eval_eq env { eq_desc } =
    match eq_desc with 
    | EQeq(p, e) -> 
       let* v = eval env e in
       let* env_p1 = matching_pattern Env.empty v p in
       return env_p1
    | EQif(e, eq1, eq2) ->
       let* v = eval env e in
       let* v = bool v in
       if v then
         let* env1 = eval_eq env eq1 in
         return env1
       else
         let* env2 = eval_eq env eq2 in
         return env2
    | EQand(eq_list) ->
       let and_eq env acc eq =
         let* env_eq = eval_eq env eq in
         let* acc = merge env_eq acc in
         return acc in
       let* env_eq = fold (and_eq env) Env.empty eq_list in
       return env_eq
    | EQreset(eq, e) -> 
       let* v = eval env e in 
       let* v = bool v in
       reset env eq v
    | EQempty -> return Env.empty
    | EQassert(e) ->
       let* v = eval env e in
       let* v = bool v in
       (* stop when [no_assert = true] *)
       if !no_assert then return Env.empty
       else if v then return Env.empty else None
    | EQlet({ l_rec; l_eq }, eq) ->
       if l_rec then None
       else
         let* l_env = eval_eq env l_eq in
         eval_eq (Env.append l_env env) eq
    | EQder _ | EQpresent _ | EQinit _
      | EQemit _ | EQlocal _ | EQautomaton _ | EQmatch _ -> None
                                                          
  and reset env eq r =
    if r then eval_eq env eq else None
    
  and match_handlers env v handlers =
    match handlers with
    | [] -> None
    | { m_pat; m_body } :: handlers ->
       let r = matching_pattern env v m_pat in
       match r with
       | None ->
          (* this is not the good handler; try an other one *)
          match_handlers env v handlers
       | Some(env_pat) ->
          let env = Env.append env_pat env in
          eval env m_body in
eval env e
