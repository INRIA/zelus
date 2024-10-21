(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Misc
open Zelus
open Value
open Ident
open Genv
open Find
open Monad
open Result
open Error

(* Computation of fixpoints *)
   
(* Dynamic check of causality. A set of equations is causal when all defined *)
(* variables are non bottom, provided free variables are non bottom *)
(* this a very strong constraint. In particular, it rejects the situation *)
(* of a variable that is bottom but not used. *)
(* causal(env)(env_out)(names) =
 *-               /\ (forall x in Dom(env), env(x) <> bot)
 *-               /\ (env_out, _ = fixpoint_eq genv sem eq n s_eq bot)
 *-               => (forall x in names /\ Dom(env_out), env_out(x) <> bot) *)
let causal loc env env_out names =
  let bot v = match v with | Vbot -> true | _ -> false in
  let bot_option v = match v with | None -> false | Some(v) -> bot v in
  let bot_name n =
    let r = find_value_opt n env_out in
    match r with | None -> false | Some(v) -> bot v in
  let bot_names =
    if Env.for_all (fun _ { cur } -> not (bot_option cur)) env
    then S.filter bot_name names else S.empty in
  if !no_causality then return ()
  else 
    if S.is_empty bot_names then return ()
    else
      error { kind = Enot_causal(bot_names); loc = loc }

(* number of variables defined by an equation *)
(* it determines the number of iterations for the computation *)
(* of the least fixpoint *)
let size { eq_write = { Defnames.dv; Defnames.di } } =
  (* [der] names do not matter because their value is computed by the solver *)
  S.cardinal dv + S.cardinal di

(* return a default value. If [default] field is present, returns it *)
(* otherwise, returns the [last] field *)
let default_value last default =
  let open Opt in
  match last, default with
  | None, None -> none
  | (_, Some(v)) | (Some(v), None) -> return v
                                    
(* given an environment [env], a local environment [env_handler] *)
(* an a set of written variables [write] *)
(* [by env env_handler write] complete [env_handler] with entries in [env] *)
(* for variables that appear in [write] *)
(* this is used for giving the semantics of a by-case definition *)
(* of streams in a control-structure, e.g.,: *)
(* [if e then do x = ... and y = ... else do x = ... done]. When [e = false] *)
(* the value of [y] is the default value given at the definition of [y] *)
(* If no default value is given (e.g., local x in ...), for the moment *)
(* we raise an error *)
let by loc env env_handler write =
  S.fold
    (fun x acc ->
      (* if [x in env] but not [x in env_handler] *)
      (* then either [x = last x] or [x = default(x)] depending *)
      (* on what is declared for [x]. *)
      let* { last; default } =
        Env.find_opt x env |>
          Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = loc } in
      if Env.mem x env_handler then acc
      else
        let* acc = acc in
        let* v =
          default_value last default |>
            Opt.to_result ~none:{ kind = Eno_default(x); loc = loc } in
        return (Env.add x { Match.empty with cur = Some(v) } acc))
    write (return env_handler) 
       
(* given [env_in] and [env_eq = [x1 \ { cur1 },..., xn \ { curn }] *)
(* returns [x1 \ { cur1; default x env; last1 },..., *)
(* xn \ { curn; default x env; lastn }]. [lasti] is the definition in *)
(* [env_eq], if [reinit = true]; otherwise, it is that of [env_in] *)
let merge v_eq v_in =
  match v_eq, v_in with
  | None, _ -> v_in
  | Some _, _ -> v_eq
  
let complete env_in env_eq =
  Env.fold
    (fun x ({ cur; last } as entry) acc ->
      match Env.find_opt x env_in with
      | None -> Env.add x entry acc
      | Some { cur = cur_in; default; last = last_in } ->
         let cur = merge cur cur_in in
         let last = merge last last_in in
         Env.add x { entry with cur; last; default } acc)
    env_eq Env.empty

(* equality of values in the fixpoint iteration. Because of monotonicity *)
(* only compare bot/nil with non bot/nil values. *)
let equal_values v1 v2 =
  match v1, v2 with
  | (Value _, Value _) | (Vbot, Vbot) | (Vnil, Vnil) -> true
  | _ -> false

(* bounded fixpoint combinator *)
(* computes a fixpoint [rec (v_out, v), s' = f s v] *)
let fixpoint loc n stop f s bot =
  let rec fixpoint n v =
    if n <= 0 then (* this case should not happen *)
      error { kind = Efixpoint_limit; loc }
    else
      (* compute a fixpoint for the value [v] keeping the current state *)
      let* (v_out, v'), s' = f s v in
      if stop v v' then return (n, (v_out, v'), s') 
      else fixpoint (n-1) v' in      
  (* computes the next state *)
  fixpoint n bot

(* Invariant: values in the environment are restricted by construction *)
(* to be either bot, nil or a primitive (atomic) value, i.e., a value *)
(* which is fully defined *)
(* stop the fixpoint when two successive environments are equal *)
let equal_opt_values v1 v2 =
  match v1, v2 with
  | (None | Some _), None  | None, Some _ -> true 
  | Some(v1), Some(v2) -> equal_values v1 v2
      
let equal_entries 
      { cur = cur1; last = last1; reinit = r1 }
      { cur = cur2; last = last2; reinit = r2 } =
    (equal_opt_values cur1 cur2) && 
      (if r1 || r2 then equal_opt_values last1 last2 else true)

let stop env_in env_out = Env.equal equal_entries env_in env_out

(* bounded fixpoint (at most [n]) for a set of mutually recursive equations *)
(* [rec env_eq, s' = (sem genv (append env_eq env) eq s)] *)
let eq genv env sem eq n s_eq bot =
  let sem s_eq env_in =
    Debug.print_ienv "Before step: env_in = " env_in;
    let env = Env.append env_in env in
    let* env_eq, s_eq = sem genv env eq s_eq in
    Debug.print_ienv "After step: env_eq = " env_eq;
    let env_eq = complete env_in env_eq in
    Debug.print_ienv "After step: env_eq = " env_eq;
    return ((Env.empty, env_eq), s_eq) in
  let* m, (_, env_eq), s_eq = 
    fixpoint eq.eq_loc n stop sem s_eq bot in
  return (env_eq, s_eq)

(* bounded fixpoint (at most [n]) for a local declaration. Equality *)
(* is limited to the names defined locally in [local x1,...,xn do eq] *)
(* [rec (env_not_x, env_x), s' = (sem genv (append env_x env) eq s)] *)
let local genv env sem eq n s_eq bot_x =
  let sem s_eq env_in_x =
    Debug.print_ienv "Before step: env_in = " env_in_x;
    let env = Env.append env_in_x env in
    let* env_eq, s_eq = sem genv env eq s_eq in
    (* split the resulting environment *)
    let env_eq_x, env_eq_not_x = 
      Env.partition (fun x _ -> Env.mem x env_in_x) env_eq in
    Debug.print_ienv "After step: env_eq_x = " env_eq_x;
    let env_eq_x = complete env_in_x env_eq_x in
    Debug.print_ienv "After step: env_eq_x = " env_eq_x;
    Debug.print_ienv "After step: env_eq_not_x = " env_eq_not_x;
    return ((env_eq_not_x, env_eq_x), s_eq) in
  Debug.print_ienv "Before fixpoint: bot_x = " bot_x;
  let* m, (env_eq_not_x, env_eq_x), s_eq = 
    fixpoint eq.eq_loc n stop sem s_eq bot_x in
  Debug.print_ienv "After fixpoint: env_eq_not_x = " env_eq_not_x;
  Debug.print_ienv "After fixpoint: env_eq_x = " env_eq_x;  
  Debug.print_state "After fixpoint: state = " s_eq;
  return ((env_eq_not_x, env_eq_x), s_eq)

(* fixpoint for mutually recursive definitions of size parameterized functions *)
(* [defs = [f1\Vsfun ...; fk\Vsfun ...]] *)
let sizefixpoint defs =
  Ident.Env.mapi 
    (fun f entry -> Match.entry (Vsizefix { bound = None; name = f; defs })) 
    defs
