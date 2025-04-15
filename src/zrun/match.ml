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

(* Pattern matching *)
open Zelus
open Value
open Monad
open Opt
open Ident

(* auxiliary functions for environments *)
let empty = { cur = None; last = None; default = None; reinit = false }
let entry v = { empty with cur = Some(Value(v)) }
let lift f env =
  Env.map (fun v -> { empty with cur = Some (f v) }) env
let liftid env = lift (fun x -> x) env
let liftv env = lift (fun v -> Value(v)) env
let unlift env = Env.map (fun { cur } -> cur) env

(* the set of names defined in a environment *)
let names_env env = Env.fold (fun n _ acc -> S.add n acc) env S.empty

let names eq_write = Defnames.names S.empty eq_write

(* match a value [v] against a pattern [p] *)
let pmatch v p =
  let rec pmatch acc v { pat_desc } =
    match v, pat_desc with
    | _, Etypeconstraintpat(p, _) -> pmatch acc v p
    | _, Evarpat(x) ->
       return (Env.add x v acc)
    | _, Ewildpat -> return acc
    | _, Ealiaspat(p, x) ->
       let* acc = pmatch acc v p in
       return (Env.add x v acc)
    | _, Eorpat(p1, p2) ->
       let env = pmatch acc v p1 in
       let acc =
         match env with
         | None -> pmatch acc v p2
         | Some(env) -> return env in
       acc
    | Vrecord(l_v_list), Erecordpat(l_p_list) ->
       let rec find l = function
         | [] -> none
         | { label; arg = v } :: p_v_list ->
            if l = label then return v else find l p_v_list in
       Opt.fold
         (fun acc { label; arg = p } ->
           let* v = find label l_v_list in
           pmatch acc v p) acc l_p_list
    | Vint(v1), Econstpat(Eint(v2)) when v1 = v2 -> return acc
    | Vbool(v1), Econstpat(Ebool(v2)) when v1 = v2 -> return acc
    | Vfloat(v1), Econstpat(Efloat(v2)) when v1 = v2 -> return acc
    | Vchar(v1), Econstpat(Echar(v2)) when v1 = v2 -> return acc
    | Vstring(v1), Econstpat(Estring(v2)) when v1 = v2 -> return acc
    | Vvoid, Econstpat(Evoid) -> return acc
    | Vconstr0(f), Econstr0pat(g) when Lident.compare f g = 0 ->
       return acc
    | Vstuple(v_list), Etuplepat(p_list) ->
       pmatch_list acc v_list p_list
    | Vconstr1(f, v_list), Econstr1pat(g, p_list) when Lident.compare f g = 0 ->
       pmatch_list acc v_list p_list
    | _ -> none

  and pmatch_list acc v_list p_list = Opt.fold2 pmatch acc v_list p_list in

  pmatch Env.empty v p

(* pattern matching for equations [p = e] and function application *)
(* [v] is an star value; [p] is a pattern but pattern matching *)
(* should not fail. In the case of a failure, this is considered as *)
(* a typing error *)
let pmatcheq v p =
  let rec pmatcheq acc v { pat_desc } =
    match v, pat_desc with
    | Vstuple(v_list), Etuplepat(l_list) ->
       pmatcheq_list acc v_list l_list
    | Vrecord(l_v_list), Erecordpat(l_p_list) ->
       let rec find l = function
         | [] -> none
         | { label; arg = v } :: p_v_list ->
            if l = label then return v else find l p_v_list in
       Opt.fold
         (fun acc { label; arg = p } ->
           let* v = find label l_v_list in
           pmatcheq acc v p) acc l_p_list
    | _, Evarpat(x) ->
       return (Env.add x v acc)
    | _, Ewildpat -> return acc
    | _, Ealiaspat(p, x) ->
       let* acc = pmatcheq acc v p in
       return (Env.add x v acc)
    | _ -> none
  and pmatcheq_list acc v_list p_list =
    match v_list, p_list with
    | [], [] -> return acc
    | v :: v_list, p :: p_list  ->
       let* acc = pmatcheq acc v p in
       pmatcheq_list acc v_list p_list
    | _ -> none in
  pmatcheq Env.empty v p

(* Pattern matching of a signal *)
let matchsig vstate p =
  match vstate with
  | Vabsent -> return (Vbool(false), Env.empty)
  | Vpresent(v) ->
     let* env = pmatcheq v p in
     return (Vbool(true), env)
  | _ -> none

(* match a state f(v1,...,vn) against a state name f(x1,...,xn) *)
let matchstate ps { desc; loc } =
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

(* Auxiliary functions to lift bottom and nil to environments *)
(* the bottom environment *)
let bot_env (eq_write: Defnames.defnames) : 'a star ientry Env.t =
  S.fold
    (fun x acc -> Env.add x { empty with cur = Some(Vbot) } acc)
    (names eq_write) Env.empty

(* the nil environment *)
let nil_env (eq_write: Defnames.defnames) : 'a star ientry Env.t =
  S.fold
    (fun x acc -> Env.add x { empty with cur = Some(Vnil) } acc)
    (names eq_write) Env.empty

(* a bot/nil value lifted to lists *)
let bot_list l = List.map (fun _ -> Vbot) l

let sbot_list l = List.map (fun _ -> Sbot) l
let snil_list l = List.map (fun _ -> Snil) l

(* a bot/nil value lifted to patterns *)
let rec distribute v acc { pat_desc } =
  match pat_desc with
  | Evarpat(x) -> Env.add x v acc
  | Etuplepat(p_list) | Econstr1pat(_, p_list) | Earraypat(p_list)->
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

(* Pattern matching for equations *)
let matcheq (v: 'a star) (p: _ pattern) : 'a star ientry Env.t Opt.t =
  let rec matchrec acc v ({ pat_desc; pat_loc } as p) =
    match v with
    | Vbot -> return (Env.append (liftid (pbot p)) acc)
    | Vnil -> return (Env.append (liftid (pnil p)) acc)
    | Value(v) ->
       match v, pat_desc with
       | Vtuple(v_list), Etuplepat(l_list) ->
          match_list acc v_list l_list
       | _ ->
          let* env = pmatch v p in
          return (Env.append (liftv env) acc)
  and match_list acc v_list l_list =
    Opt.fold2 matchrec acc v_list l_list in
  matchrec Env.empty v p

let matchsig (v: 'a star) ({ pat_loc } as p : _ pattern) :
      ('a star * 'a star ientry Env.t) Opt.t =
  match v with
  | Vbot ->
     return (Vbot, liftid (pbot p))
  | Vnil ->
     return (Vnil, liftid (pnil p))
  | Value(v) ->
     let* v, env = matchsig v p in
     return (Value(v), liftv env)

(* definition [fun (x11,...) ... (xn1,...) returns (y1,...) eq] *)
(* arg_in_1 = [x11;...]; ...; arg_in_n = [xn1;...]; arg_out = [y1;...] *)
(* computes the matching of [v] with [arg]. The resulting substitution is *)
(* added to [env] *)
let matching_arg_in loc env arg v =
  let open Result in
  let open Error in
  let match_in acc { var_name } v =
    return (Env.add var_name { empty with cur = Some(v) } acc) in
  match arg, v with
  | l, Vbot ->
     fold2 { kind = Epattern_matching_failure; loc = loc }
       match_in env l (List.map (fun _ -> Vbot) l)
  | l, Vnil ->
     fold2 { kind = Epattern_matching_failure; loc = loc }
       match_in env l (List.map (fun _ -> Vnil) l)
  | [], Value(Vvoid) -> return env
  | l, Value(Vtuple(v_list)) ->
     fold2
       { kind = Epattern_matching_failure; loc = loc }
       match_in env l v_list
  | l, Value(Vstuple(v_list)) ->
     fold2
       { kind = Epattern_matching_failure; loc = loc }
       (fun acc n pvalue -> match_in acc n (Value(pvalue))) env l v_list
  | [x], _ -> match_in env x v
  | _ ->
     (* type error *)
     error { kind = Epattern_matching_failure; loc = loc }

let matching_arg_out loc env arg =
  let open Result in
  let open Error in
  let match_out { var_name } =
    Find.find_value_opt var_name env |>
      Opt.to_result ~none:{ kind = Eunbound_ident(var_name); loc = loc } in
  let* v_list =
    map match_out arg in
  match v_list with
  | [] -> return Primitives.void
  | [v] -> return v
  | _ -> return (Value(Vtuple(v_list)))

(* Pattern matching - returns the selected handler and substitution or fail *)
let select loc genv env ve handlers =
  let open Result in
  let open Error in
  let rec match_rec handlers =
    match handlers with
    | [] -> error { kind = Epattern_matching_failure; loc = loc }
    | { m_pat; m_body } :: handlers ->
       let r = pmatch ve m_pat in
       match r with
       | None ->
          (* this is not the good handler; try an other one *)
          match_rec handlers
       | Some(env_pat) -> 
          return (env_pat, m_body) in
  match_rec handlers

let match_handler_list loc body genv env ve handlers =
  let open Result in
  let* env_pat, m_body = select loc genv env ve handlers in
  let env_pat = liftv env_pat in
  let env = Env.append env_pat env in
  body genv env m_body



