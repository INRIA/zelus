(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2018                                               *)
(*                                                                        *)
(*  Marc Pouzet   Timothy Bourke                                          *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(** static evaluation of expressions *)
(** The result is a collection of first-order monomorphic functions *)
(** and a value *)

open Ident
open Deftypes
open Global
open Zelus
open Zaux

type exp_or_eq =
  | Exp of exp
  | Eq of eq

exception NotStatic of exp_or_eq
exception TypeError

(** Remove entries in the type environment of a block *)
(* for names that appear in the evaluation environment *)
let remove tenv env_closure =
  Env.filter (fun n _ -> not (Env.mem n env_closure)) tenv

(** Pattern matching *)
let record_access { value_exp = value_exp } ln =
  try
    match value_exp with
    | Vrecord(l_v_list) -> List.assoc (Modules.qualident ln) l_v_list
    | _ -> raise TypeError
  with
  | _ -> raise TypeError
	    
(** Pattern matching. [matches env p v = env'] returns an extended *)
(* environment [env'] such that [env'(p) = v] *)
let rec matches env { p_desc = desc } ({ value_exp = v_exp } as v) =
  (* find the value associated to a label *)
  let rec find qid = function
    | [] -> raise TypeError
    | (qid_v, v) :: p_v_list ->
       if qid = qid_v then v else find qid p_v_list in
  match desc, v_exp with
  | Ewildpat, _ -> env
  | Econstpat(i), Vconst(j) when i = j -> env
  | Econstr0pat(c1), Vconstr0(qid) when (Modules.qualident c1) = qid -> env
  | Etuplepat(p_list), Vtuple(v_list) ->
     begin try List.fold_left2 matches env p_list v_list
	   with _ -> raise TypeError
     end
  | Evarpat(n), _ -> Env.add n v env
  | Ealiaspat(p, n), _ -> matches (Env.add n v env) p v
  | Eorpat(p1, p2), _ ->
     begin try matches env p1 v with TypeError -> matches env p2 v end
  | Erecordpat(l_p_list), Vrecord(p_v_list) ->
     begin try
	 List.fold_left
	   (fun env (ln, p) ->
	    matches env p (find (Modules.qualident ln) p_v_list)) env l_p_list
       with _ -> raise TypeError
     end
  | Etypeconstraintpat(p, _), _ -> matches env p v
  | _ -> raise TypeError

(** [select env v m_b_list = b] where
 * - env is a environment;
 * - v a value;
 * - m_b_list a list of pattern * block;
 * - b a block whose pattern matches v and is the first in the list *)
let select env v m_b_list =
  let rec loop = function
    | [] -> raise TypeError
    | { m_pat = p; m_body = b } :: m_b_list ->
       try
	 let env = matches env p v in env, b
       with
       | TypeError -> loop m_b_list in
  loop m_b_list

(** Evaluate an expression. [expression env e = v] *)
(* - e is a static expression;
 * - env an environment;
 * - v a value *)
let rec expression env ({ e_desc = desc; e_loc = loc } as e) =
  match desc with
  | Econst(i) -> Global.value_code (Vconst(i))
  | Econstr0(c) -> Global.value_code (Vconstr0(Modules.qualident c))
  | Eglobal { lname = lname } ->
     let { info = { value_code = v } } =
       try Modules.find_value lname
       with Not_found -> raise (NotStatic (Exp e)) in
     v
  | Elocal(n) ->
     let v =
       try Env.find n env with Not_found -> raise (NotStatic (Exp e)) in v
  | Etuple(e_list) ->
     Global.value_code (Vtuple(List.map (expression env) e_list))
  | Erecord(n_e_list) -> 
     let v_exp =
       Vrecord(List.map
		 (fun (ln, e) -> (Modules.qualident ln, expression env e))
		 n_e_list) in
     Global.value_code v_exp
  | Erecord_access(e, ln) ->
     record_access (expression env e) ln
  | Eop _ | Elast _ -> raise (NotStatic (Exp e))
  | Eapp(_, e, e_list) ->
     let v = expression env e in
     let v_list = List.map (expression env) e_list in
     app v v_list
  | Etypeconstraint(e, _) -> expression env e
  | Eseq(e1, e2) ->
     ignore (expression env e1); expression env e2
  | Eperiod(p) -> Global.value_code (Vperiod(p))
  | Elet(l, e_let) ->
     let env = local env l in
     expression env e_let
  | Eblock _ -> raise (NotStatic (Exp e))
  | Epresent _ | Ematch _ -> assert false
	    
(** Evaluate an application *)
and app ({ value_exp = value_exp } as v) v_list =
  (* [arguments env_closure p_list v_list = p_list', env'] *)
  (* returns the environment for evaluating the body *)
  (* and the list of patterns that have not been consummed *)
  let rec arguments env_closure p_list v_list =
    match p_list, v_list with
    | [], [] -> [], env_closure
    | p :: p_list, v :: v_list ->
       arguments (matches env_closure p v) p_list v_list
    | [], _ -> raise TypeError
    | p_list, [] -> p_list, env_closure in
  match value_exp, v_list with
  | _, [] ->
     (* if [v_list = []], the result is [v] *)
     v
  | Vfun({ f_args = p_list; f_body = e; f_env = fenv } as funexp, env_closure),
    _ ->
     let p_list, env_closure = arguments env_closure p_list v_list in
     if p_list = [] then expression env_closure e
     else
       (* remove entries from [fenv] that are in the environment of values *)
       let fenv = remove fenv env_closure in
       Global.value_code
	    (Vfun({ funexp with f_args = p_list; f_env = fenv }, env_closure))
  | (* two integer arithmetic operations are implemented: *)
    (* addition and subtraction are used in array size expressions *)
    Vabstract(op),
    [{ value_exp = Vconst(Eint(i1)) }; { value_exp = Vconst(Eint(i2)) }] ->
     let i = if op = Initial.pervasives_name "+" then i1 + i2
	     else if op = Initial.pervasives_name "-" then i1 - i2
	     else raise TypeError in
     value_code (Vconst(Eint(i)))
  | _ -> raise TypeError

(** Evaluate all the definitions and returns an environment *)
and local env { l_eq = eq_list } =
  List.fold_left equation env eq_list

(** Reduce an equation. *)
and equation env ({ eq_desc = desc; eq_loc = loc } as eq) = 
  match desc with
  | EQeq(p, e) -> matches env p (expression env e)
  | EQmatch(total, e, m_b_list) ->
     let v = expression env e in
     let env, b = select env v m_b_list in
     block env b
  | EQblock(b) -> block env b
  | EQand(eq_list) 
  | EQbefore(eq_list) -> List.fold_left equation env eq_list
  | EQpluseq _ | EQinit _ | EQnext _
  | EQder _ | EQreset _ | EQpresent _
  | EQemit _ | EQautomaton _ | EQforall _ -> raise (NotStatic (Eq eq))
						   
and block env { b_locals = l_list; b_body = eq_list } =
  let env = List.fold_left local env l_list in
  List.fold_left equation env eq_list
