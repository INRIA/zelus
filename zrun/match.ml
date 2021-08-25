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

(* Pattern matching *)
open Zelus
open Value
open Monad
open Opt
open Ident
   
(* match a value [v] against a pattern [p] *)
let pmatching (v : pvalue) (p : pattern) =
  let rec matchrec acc v { pat_desc } =
    match v, pat_desc with
    | _, Etypeconstraintpat(p, _) -> matchrec acc v p
    | _, Evarpat(x) ->
       return (Env.add x v acc)
    | _, Ewildpat -> return acc
    | _, Ealiaspat(p, x) ->
       let* acc = matchrec acc v p in
       return (Env.add x v acc)
    | _, Eorpat(p1, p2) ->
       let env = matchrec Env.empty v p1 in
       let acc =
         match env with
         | None -> matchrec acc v p2
         | Some(env) -> return (Env.append env acc) in
       acc
    | Vrecord(l_v_list), Erecordpat(l_p_list) ->
       let rec find l = function
         | [] -> none
         | { label; arg = v } :: p_v_list ->
            if l = label then return v else find l p_v_list in
       Opt.fold
         (fun acc { label; arg = p } ->
           let* v = find label l_v_list in
           matchrec acc v p) acc l_p_list
    | Vint(v1), Econstpat(Eint(v2)) when v1 = v2 -> return Env.empty
    | Vbool(v1), Econstpat(Ebool(v2)) when v1 = v2 -> return Env.empty
    | Vfloat(v1), Econstpat(Efloat(v2)) when v1 = v2 -> return Env.empty
    | Vchar(v1), Econstpat(Echar(v2)) when v1 = v2 -> return Env.empty
    | Vstring(v1), Econstpat(Estring(v2)) when v1 = v2 -> return Env.empty
    | Vvoid, Econstpat(Evoid) -> return Env.empty
    | Vconstr0(f), Econstr0pat(g) when Lident.compare f g = 0 ->
       return Env.empty
    | Vstuple(v_list), Etuplepat(p_list) ->
       matchrec_list acc v_list p_list
    | Vconstr1(f, v_list), Econstr1pat(g, p_list) when Lident.compare f g = 0 ->
       matchrec_list acc v_list p_list
    | _ -> none
         
  and matchrec_list acc v_list p_list =
    Opt.fold2 matchrec acc v_list p_list in
  (* main entry *)
  matchrec Env.empty v p
  
(* pattern matching for equations [p = e] and function application *)
(* [v] is an extended value; [p] is a pattern but pattern matching *)
(* should not fail. In the case of a failure, this is considered as *)
(* a typing error *)
let matcheq (v : pvalue) (p : pattern) : pvalue Env.t Opt.t =
  let rec matchrec acc v { pat_desc } =
    match v, pat_desc with
    | Vstuple(v_list), Etuplepat(l_list) ->
       match_list acc v_list l_list
    | Vrecord(l_v_list), Erecordpat(l_p_list) ->
       let rec find l = function
         | [] -> none
         | { label; arg = v } :: p_v_list ->
            if l = label then return v else find l p_v_list in
       Opt.fold
         (fun acc { label; arg = p } ->
           let* v = find label l_v_list in
           matchrec acc v p) acc l_p_list
    | _, Evarpat(x) ->
       return (Env.add x v acc)
    | _, Ewildpat -> return acc
    | _, Ealiaspat(p, x) ->
       let* acc = matchrec acc v p in
       return (Env.add x v acc)
    | _ -> none
  and match_list acc v_list p_list =
    match v_list, p_list with
    | [], [] -> return acc
    | v :: v_list, p :: p_list  ->
       let* acc = matchrec acc v p in
       match_list acc v_list p_list 
    | _ -> none in
  matchrec Env.empty v p

(* Pattern matching of a signal *)
let matchsig (vstate: pvalue) (p: pattern) : (pvalue * pvalue Env.t) Opt.t =
  match vstate with
  | Vabsent -> return (Vbool(false), Env.empty)
  | Vpresent(v) ->
     let* env = matcheq v p in
     return (Vbool(true), env)
  | _ -> none
  
(* match a state f(v1,...,vn) against a state name f(x1,...,xn) *)
let matchstate (ps : pvalue) ({ desc; loc } : statepat) : (pvalue Env.t) Opt.t =
  match ps, desc with
  | Vstate0(f), Estate0pat(g) when Ident.compare f g = 0 -> return Env.empty
  | Vstate1(f, v_list), Estate1pat(g, id_list) when
         (Ident.compare f g = 0) &&
           (List.length v_list = List.length id_list) ->
     let env =
       List.fold_left2
         (fun acc v x -> Env.add x v  acc)
         Env.empty v_list id_list in
     return env
  | _ -> none
  
