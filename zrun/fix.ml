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

open Smisc
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
let causal loc (env: value ientry Env.t) (env_out: value ientry Env.t ) names =
  let l1 = Env.bindings env in
  let l2 = Env.bindings env_out in
  let bot v = match v with | Vbot -> true | _ -> false in
  let bot_name n =
    let r = find_value_opt n env_out in
    match r with | None -> false | Some(v) -> bot v in
  let bot_names =
    if Env.for_all (fun _ { cur } -> not (bot cur)) env
    then S.filter bot_name names else S.empty in
  if !set_nocausality then return ()
  else 
    if S.is_empty bot_names then return ()
    else
      error { kind = Enot_causal(bot_names); loc = loc }

(* number of variables defined by an equation *)
(* it determines the number of iterations for the computation *)
(* of the least fixpoint *)
let size { eq_write } = S.cardinal (Deftypes.names S.empty eq_write)

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
(* this is used for giving the semantics of a control-structure, e.g.,: *)
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
      let* { last; default } as entry =
        Env.find_opt x env |>
          Opt.to_result ~none:{ kind = Eunbound_ident(x); loc = loc } in
      if Env.mem x env_handler then acc
      else
        let* acc = acc in
        let* v =
          default_value last default |>
            Opt.to_result ~none:{ kind = Eno_default(x); loc = loc } in
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
(* returns [x1 \ { cur1; default x env },..., xn \ { curn; default x env }] *)
let complete_with_default env env_handler =
  Env.fold
    (fun x ({ cur } as entry) acc ->
      match Env.find_opt x env with
      | None -> Env.add x entry acc
      | Some { last; default } ->
         Env.add x { entry with last = last; default = default } acc)
    env_handler Env.empty

(* equality of values in the fixpoint iteration. Because of monotonicity *)
(* only compare bot/nil with non bot/nil values. *)
let equal_values v1 v2 =
  match v1, v2 with
  | (Value _, Value _) | (Vbot, Vbot) | (Vnil, Vnil) -> true
  | _ -> false

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
(* stop the fixpoint when two successive environments are equal *)
let equal_env env1 env2 =
  Env.equal
    (fun { cur = cur1} { cur = cur2 } -> equal_values cur1 cur2)
    env1 env2

(* bounded fixpoint for a set of equations *)
let eq genv env sem eq n s_eq bot =
  let sem s_eq env_in =
    let l1 = Env.bindings env_in in
    Sdebug.print_ienv "Before step" env_in;
    let env = Env.append env_in env in
    let l2 = Env.bindings env in
    let* env_out, s_eq = sem genv env eq s_eq in
    let l3 = Env.bindings env_out in
    Sdebug.print_ienv "After step" env_out;
    let env_out = complete_with_default env env_out in
    let l4 = Env.bindings env_out in
    return (env_out, s_eq) in
  let* m, env_out, s_eq = fixpoint n equal_env sem s_eq bot in
  return (env_out, s_eq)
