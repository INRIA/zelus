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
open Error
open Monad
open Result
open Ident
open Find
open Zelus
open Value
open Primitives
open Match
open Sdebug

       
(* merge two environments provided they do not overlap *)
let merge loc env1 env2 =
  let s = Env.to_seq env1 in
  seqfold
    (fun acc (x, entry) ->
      if Env.mem x env2 then error { kind = Emerge_env; loc = loc }
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

(* check assertion *)
let check_assertion loc ve ret =
  (* when ve is not bot/nil it must be true *)
  match ve with
  | Vnil | Vbot -> return ret
  | Value(v) ->
     let* v = bool v |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
     (* stop when [no_assert = true] *)
     if !no_assert || v then return ret 
     else error { kind = Eassert_failure; loc = loc }

     
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

(* [let*+ x = e in e'] composes [let*] and [let+] *)
let (let*+) v f =
  let* v = v in
  let+ v = v in
  f v

(* array operations *)
let concat loc v1 v2 =
  let concat v1 v2 =
    match v1, v2 with
    | Vflat(v1), Vflat(v2) ->
       return (Value(Varray(Vflat(Array.append v1 v2))))
    | Vmap { m_length = l1; m_u = mu1}, Vmap { m_length = l2; m_u = mu2 } ->
       let m_length = l1 + l2 in
       let m_u i = if i <= l1 then mu1 i else mu2 (i - l1) in
       return (Value(Varray(Vmap { m_length; m_u })))
    | Vmap { m_length; m_u }, Vflat(v) ->
       let m_u i = if i <= m_length
                   then m_u i else return (v.(i - m_length)) in
       let m_length = m_length + Array.length v in
       return (Value(Varray(Vmap { m_length; m_u })))
    | Vflat(v), Vmap { m_length; m_u } ->
       let lv = Array.length v in
       let m_length = m_length + lv in
       let m_u i = if i <= lv then return (v.(i)) else m_u (i - lv) in
       return (Value(Varray(Vmap { m_length; m_u }))) in
  let+ v1 = v1 and+ v2 = v2 in
  match v1, v2 with
  | Varray(v1), Varray(v2) ->
     concat v1 v2
  | _ -> error { kind = Etype; loc }
       
let get_in_array loc a i =
  match a with
  | Vflat(a) ->
     let n = Array.length a in
     if (i >= 0) && (i < n) then return (a.(i))
     else error { kind = Earray_size { size = n; index = i }; loc }
  | Vmap { m_length; m_u } ->
     if (i >= 0) && (i < m_length) then m_u i
     else error { kind = Earray_size { size = m_length; index = i }; loc }

let get loc v i =
  let+ v = v and+ i = i in
  match v, i with
  | Varray(a), Vint(i) ->
     let* v = get_in_array loc a i in
     return (Value(v))
  | _ -> error { kind = Etype; loc }

let get_with_default loc v i default =
  let get a i =
    match a with
    | Vflat(a) ->
       let n = Array.length a in
       if (i >= 0) && (i < n) then return (Value(a.(i)))
       else return default
    | Vmap { m_length; m_u } ->
       if (i >= 0) && (i < m_length) then
         let* v = m_u i in return (Value(v))
       else return default in
  let+ v = v and+ i = i in
  match v, i with
  | Varray(a), Vint(i) -> get a i
  | _ -> error { kind = Etype; loc }

let slice loc v i1 i2 =
  let slice v i1 i2 = match v with
    | Vflat(a) ->
       let n = Array.length a in
       if i1 < n then
         if i2 < n then
           return (Value(Varray(Vflat(Array.sub a i1 (i2 - i1 + 1)))))
         else error { kind = Earray_size { size = n; index = i2 }; loc }
       else error { kind = Earray_size { size = n; index = i1 }; loc }
    | Vmap { m_length; m_u } ->
       if i1 < m_length then
         if i2 < m_length then
           return (Value(Varray(Vmap { m_length = i2 - i1 + 1; m_u })))
         else
           error { kind = Earray_size { size = m_length; index = i2 }; loc }
       else error { kind = Earray_size { size = m_length; index = i1 }; loc } in
  let+ v = v and+ i1 = i1 and+ i2 = i2 in
  match v, i1, i2 with
  | Varray(v), Vint(i1), Vint(i2) -> slice v i1 i2
  | _ -> error { kind = Etype; loc }
       
(* [| v with i <- w |] *)
let update loc v i w =
  let update v i w =
    match v with
    | Vflat(a) ->
       if (i >= 0) && (i < Array.length a) then
         let a = Array.copy a in
         a.(i) <- w;
         return (Vflat(a)) else return v
    | Vmap { m_length; m_u } ->
       return
         (Vmap { m_length; m_u = fun j -> if i = j then return w else m_u j }) in
  let+ a = v and+ i = i and+ w = w in
  match a, i with
  | Varray(a), Vint(i) ->
     let* a = update a i w in
     return (Value(Varray(a)))
  | _ -> error { kind = Etype; loc }
       
(* [| v with i1,..., in <- w |] is a shortcut for *)
(* [| v with i1 <- [| v.(i1) with i2,...,in <- w |] |] *)
let rec update_list loc v i_list w =
  match i_list with
  | [] -> error { kind = Eunexpected_failure; loc }
  | i :: i_list ->
     let* w = match i_list with
       | [] -> return w
       | _ -> let* v = get loc v i in
              update_list loc v i_list w in
     update loc v i w

(* conversion between a flat array and a map *)
let map_o_flat loc v =
  match v with
  | Vflat(f) ->
     return
       (Vmap { m_length = Array.length f; m_u = fun i -> return (f.(i)) })
  | Vmap _ -> return v
let flat_of_map_array loc v =
  let fill length a m_u =
    let rec fillrec length =
      if length = 0 then return a
      else let* v = m_u length in a.(length) <- v; fillrec (length - 1) in
    fillrec length in
  match v with
    | Vflat _ -> return v
    | Vmap { m_length; m_u } ->
       if m_length = 0 then return (Vflat([||]))
       else let* v = m_u 0 in
            let a = Array.make m_length v in
            let* v = fill m_length a m_u in
            return (Vflat v)

(* transpose. [transpose v = \j:[n].\i:[m].v[i][j]] *)
let dim v =
  match v with
    | Vflat(a) -> Array.length a, fun i -> return a.(i)
    | Vmap { m_length; m_u } -> m_length, m_u
  
(* [v i j] *)
let get_get loc v i j =
  let* v = get_in_array loc v i in
  match v with
  | Varray(v) -> get_in_array loc v j
  | _ -> error { kind = Etype; loc }

let dim_dim loc a =
  let m, u_v = dim a in
  let* a = u_v 0 in
  match a with
  | Varray(v) -> let n, _ = dim v in return (m, n)
  | _ -> error { kind = Etype; loc }

let transpose loc v =
  let+ v = v in
  match v with
  | Varray(v) ->
     let* m, n = dim_dim loc v in
     return
       (Value
          (Varray
             (Vmap
                { m_length = n;
                  m_u = fun j ->
                        return
                          (Varray(Vmap { m_length = m;
                                         m_u = fun i ->
                                               get_get loc v i j })) })))
  | _ -> error { kind = Etype; loc }
 

(* flatten: imposes that the size of internal arrays are the same, that is *)
(* flatten : 'n,'m. ['n]['m]'a -> ['n * 'm]'a *)
let flatten loc v =
  let+ v = v in
  match v with
  | Varray(v) ->
     let* m, n = dim_dim loc v in
     return
       (Value(Varray
                (Vmap
                   { m_length = m * n;
                     m_u = fun i -> let q = i / n in
                                    let r = i mod n in
                                    get_get loc v q r })))
  | _ -> error { kind = Etype; loc }
     
(* reverse *)
let reverse loc v =
  let+ v = v in
  match v with
  | Varray(v) ->
     let n, u = dim v in
     return
       (Value(Varray
                (Vmap
                   { m_length = n;
                     m_u = fun i -> get_in_array loc v (n - i) })))
  | _ -> error { kind = Etype; loc }
 
(* check that a value is an integer *)
let int loc v =
  let* v = Primitives.pvalue v |>
             Opt.to_result ~none: { kind = Etype; loc } in
  (* and an integer value *)
  Primitives.int v |> Opt.to_result ~none: { kind = Etype; loc}
  
(* Pattern matching *)
let match_handler_list loc body genv env ve handlers =
  let rec match_rec handlers =
    match handlers with
    | [] -> error { kind = Epattern_matching_failure; loc = loc }
    | { m_pat; m_body } :: handlers ->
       let r = Match.pmatch ve m_pat in
       match r with
       | None ->
          (* this is not the good handler; try an other one *)
          match_rec handlers
       | Some(env_pat) ->
          let env_pat = liftv env_pat in
          let env = Env.append env_pat env in
          body genv env m_body in
  match_rec handlers
       

(* evaluation function *)
let rec exp genv env { e_desc; e_loc } =
  match e_desc with   
  | Econst(v) ->
     return (Value(immediate v))
  | Econstr0 { lname } ->
     return (Value(Vconstr0(lname)))
  | Elocal x ->
     find_value_opt x env |>
       Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = e_loc }     
  | Eglobal { lname } ->
     let* v =
       find_gvalue_opt lname genv |>
         Opt.to_result ~none:{ kind = Eunbound_lident(lname); loc = e_loc } in
     return (Value(v))
  | Eop(op, e_list) ->
     begin match op, e_list with
     | Eifthenelse, [e1; e2; e3] ->
        let*+ v1 = exp genv env e1 in
        begin match v1 with
        | Vbool(b) ->
           if b then exp genv env e2 else exp genv env e3
        | _ -> error { kind = Etype; loc = e_loc } end
     | _ -> error { kind = Eshould_be_combinatorial; loc = e_loc }
     end
  | Econstr1 { lname; arg_list } ->
     let* v_list = exp_list genv env arg_list in
     let+ v_list = Primitives.slist v_list in
     return (Value(Vconstr1(lname, v_list)))
  | Etuple(e_list) ->
     let* v_list = exp_list genv env e_list in
     let+ v_list = Primitives.slist v_list in
     return (Value(Vstuple(v_list)))
  | Eapp (f, e_list) ->
     let*+ fv = exp genv env f in
     let* v_list = exp_list genv env e_list in
     apply e_loc fv v_list
  | Elet({ l_rec; l_eq }, e) ->
     if l_rec then error { kind = Erecursive_value; loc = e_loc }
     else
       let* l_env = eval_eq genv env l_eq in
       exp genv (Env.append l_env env) e
  | Ematch { e; handlers } ->
     let*+ ve = exp genv env e in
     match_handler_list e_loc exp genv env ve handlers
  | Erecord_access { label; arg } ->
     let*+ arg = exp genv env arg in
     let* v = record_access { label; arg } |>
                Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     return (Value(v))
  | Erecord(r_list) ->
     let* r_list =
       map
         (fun { label; arg } ->
           let*+ arg = exp genv env arg in
           return (Value { label; arg })) r_list in
     let+ r_list = Primitives.slist r_list in
     return (Value(Vrecord(r_list)))
  | Erecord_with(r, r_list) ->
     let*+ r = exp genv env r in
     let* label_arg_list =
        get_record r |> Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     let* ext_label_arg_list =
       map
         (fun { label; arg } ->
           let*+ arg = exp genv env arg in
           return (Value { label; arg })) r_list in
     let+ ext_label_arg_list = Primitives.slist ext_label_arg_list in
     let* r =
       record_with label_arg_list ext_label_arg_list |>
         Opt.to_result ~none:{ kind = Etype; loc = e_loc } in
     return (Value(Vrecord(r)))
  | Etypeconstraint(e, _) -> exp genv env e
  | Efun(fe) -> funexp genv env fe
  | Ereset(e_body, e_res) ->
     let*+ v = exp genv env e_res in
     begin match v with
     | Vbool _ -> exp genv env e_body
     | _ -> error { kind = Etype; loc = e_loc }
     end
  | Elast x ->
     find_last_opt x env |>
       Opt.to_result ~none:{ kind = Eunbound_last_ident(x); loc = e_loc }   
  | Eassert(e_body) ->
     let* v = exp genv env e_body in
     let* r = check_assertion e_loc v void in
     return r
  | Epresent _ -> error { kind = Enot_implemented; loc = e_loc }
  | Eforloop _ -> error { kind = Enot_implemented; loc = e_loc }
                
and exp_list genv env e_list = map (exp genv env) e_list

and record_access { label; arg } =
  (* look for [label] in the value of [arg] *)
  let open Opt in
  let* record_list = get_record arg in
  let rec find l record_list =
    match record_list with
    | [] -> none
    | { label; arg } :: record_list ->
       if label = l then return arg
       else find l record_list in
  find label record_list
  
and record_with label_arg_list ext_label_arg_list = 
  let open Opt in
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
  
(* application [fv v_list] of a combinatorial function *)
and apply loc fv v_list =
  match fv, v_list with
  | _, [] -> return (Value(fv))
  | Vfun(op), v :: v_list -> apply_op loc op v v_list
  | Vclosure { c_funexp = { f_kind; f_args; f_body } as fe;
               c_genv; c_env }, _ ->
     apply_closure loc c_genv c_env fe f_args f_body v_list
  | _ ->
     (* typing error *)
     error { kind = Etype; loc = loc }

and apply_op loc op v v_list =
  let*+ v =
    Primitives.atomic v |> Opt.to_result ~none:{ kind = Etype; loc } in
  let* fv =
    op v |> Opt.to_result ~none:{ kind = Etype; loc = loc } in
  apply loc fv v_list
                                            
(* apply a closure to a list of arguments *)
and apply_closure loc genv env ({ f_kind; f_loc } as fe) f_args f_body v_list =
  match f_args, v_list with
  | [], _ ->
     (* check that the kind is combinatorial *)
     let* r =
       match f_kind with
       | Knode | Khybrid ->
          error { kind = Eshould_be_combinatorial; loc }
       | Kstatic | Kfun ->
          match v_list with
          | [] -> result genv env f_body
          | _ -> let*+ fv = result genv env f_body in
                 apply loc fv v_list in
     return r
  | arg :: f_args, v :: v_list ->
     let* env = Match.matching_arg_in f_loc env arg v in
     apply_closure loc genv env fe f_args f_body v_list
  | _, [] ->
     return
       (Value(Vclosure({ c_funexp = { fe with f_args = f_args };
                         c_genv = genv; c_env = env })))
      
(* Evaluation function for an equation *)
and eval_eq genv env { eq_desc; eq_write; eq_loc } =
  match eq_desc with 
  | EQeq(p, e) -> 
     let* v = exp genv env e in
     let* env_p1 =
       Match.matcheq v p |>
         Opt.to_result
           ~none:{ kind = Epattern_matching_failure; loc = eq_loc } in
     return env_p1
  | EQif(e, eq1, eq2) ->
     let* v = exp genv env e in
     let* env_eq =
       match v with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write)
       | Vnil -> return (nil_env eq_write)
       | Value(b) ->
          let* v =
            bool b |> Opt.to_result ~none:{ kind = Etype; loc = e.e_loc } in
          if v then
            eval_eq genv env eq1
          else eval_eq genv env eq2 in
     return env_eq
  | EQand(eq_list) ->
     let and_eq env acc eq =
       let* env_eq = eval_eq genv env eq in
       let* acc = merge eq_loc env_eq acc in
       return acc in
     let* env_eq = fold (and_eq env) Env.empty eq_list in
     return env_eq
  | EQreset(eq, e) -> 
     let* v = exp genv env e in 
     let* env_eq =
       match v with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write)
       | Vnil -> return (nil_env eq_write)
       | Value(v) ->
          let* _ =
            bool v |> Option.to_result ~none:{ kind = Etype; loc = e.e_loc } in
          eval_eq genv env eq in    
     return env_eq
  | EQempty -> return Env.empty
  | EQassert(e) ->
     let* ve = exp genv env e in
     let* r = check_assertion eq_loc ve Env.empty in
     return r
  | EQmatch { e; handlers } ->
     let* ve = exp genv env e in
     let* env =
       match ve with
       (* if the condition is bot/nil then all variables have value bot/nil *)
       | Vbot -> return (bot_env eq_write)
       | Vnil -> return (nil_env eq_write)
       | Value(ve) ->
          match_handler_list eq_loc eval_eq genv env ve handlers in 
     return env
  | EQlet({ l_rec; l_eq }, eq_let) ->
     (* no recursive value is allowed in a combinational function *)
     (* this restriction could be removed since there is no reason to do so *)
     if l_rec then error { kind = Erecursive_value; loc = eq_loc }
     else
       let* l_env = eval_eq genv env l_eq in
       eval_eq genv (Env.append l_env env) eq_let
  | EQder _ | EQinit _ | EQautomaton _ ->
     error { kind = Eshould_be_combinatorial; loc = eq_loc }
  | EQpresent _  | EQemit _ | EQlocal _ ->
     error { kind = Enot_implemented; loc = eq_loc }
  | EQforloop _ -> error { kind = Enot_implemented; loc = eq_loc }
 
and funexp genv env fe =
  Result.return (Value(Vclosure { c_funexp = fe; c_genv = genv; c_env = env }))

and block genv env { b_vars; b_body; b_loc } =
  (* For combinatorial expressions, recursive values are not allowed. *)
  let* _ =
    fold
      (fun acc { var_name; var_default; var_init } ->
        match var_default, var_init with
        | (None, None) -> return (S.add var_name acc)
        | _ ->
           (* type error *)
           error { kind = Eshould_be_combinatorial; loc = b_loc })
      S.empty b_vars in
  let* b_env = eval_eq genv env b_body in
  return (Env.append b_env env, b_env)

and result genv env { r_desc; r_loc } =
  match r_desc with
  | Exp(e) -> exp genv env e
  | Returns({ b_vars; b_loc } as b) ->
     let* env, _ = block genv env b in
     let* v = Match.matching_arg_out b_loc env b_vars in
     return v

