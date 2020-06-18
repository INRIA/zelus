(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(** static evaluation of expressions *)

open Ident
open Deftypes
open Global
open Zelus
open Zaux

type error =
  | NotStaticEq of eq
  | NotStaticExp of exp
  | TypeError

exception Error of error
    
(** Remove entries in the type environment of a block *)
(* for names that appear in the evaluation environment *)
let remove tenv env_closure =
  Env.filter (fun n _ -> not (Env.mem n env_closure)) tenv

(** Pattern matching *)
let record_access { value_exp = value_exp } ln =
  try
    match value_exp with
    | Vrecord(l_v_list) -> List.assoc (Modules.qualident ln) l_v_list
    | _ -> raise (Error(TypeError))
  with
  | _ -> raise (Error(TypeError))
	    
(** Pattern matching. [matches env p v = env'] returns an extended *)
(* environment [env'] such that [env'(p) = v] *)
let rec matches env { p_desc = desc } ({ value_exp = v_exp } as v) =
  (* find the value associated to a label *)
  let rec find qid = function
    | [] -> raise (Error(TypeError))
    | (qid_v, v) :: p_v_list ->
       if qid = qid_v then v else find qid p_v_list in
  match desc, v_exp with
  | Ewildpat, _ -> env
  | Econstpat(i), Vconst(j) when i = j -> env
  | Econstr0pat(c1), Vconstr0(qid) when (Modules.qualident c1) = qid -> env
  | Etuplepat(p_list), Vtuple(v_list) ->
     begin try List.fold_left2 matches env p_list v_list
	   with _ -> raise (Error(TypeError))
     end
  | Econstr1pat(c1, p_list), Vconstr1(qid, v_list)
                                   when (Modules.qualident c1) = qid ->
     begin try List.fold_left2 matches env p_list v_list
	   with _ -> raise (Error(TypeError))
     end
  | Evarpat(n), _ -> Env.add n v env
  | Ealiaspat(p, n), _ -> matches (Env.add n v env) p v
  | Eorpat(p1, p2), _ ->
     begin try matches env p1 v with Error(TypeError) -> matches env p2 v end
  | Erecordpat(l_p_list), Vrecord(p_v_list) ->
     begin try
	 List.fold_left
	   (fun env (ln, p) ->
	    matches env p (find (Modules.qualident ln) p_v_list)) env l_p_list
       with _ -> raise (Error(TypeError))
     end
  | Etypeconstraintpat(p, _), _ -> matches env p v
  | _ -> raise (Error(TypeError))

(** [select env v m_b_list = b] where
 * - env is a environment;
 * - v a value;
 * - m_b_list a list of pattern * block;
 * - b a block whose pattern matches v and is the first in the list *)
let select env v m_b_list =
  let rec loop = function
    | [] -> raise (Error(TypeError))
    | { m_pat = p; m_body = b } :: m_b_list ->
       try
	 let env = matches env p v in env, b
       with
       | Error(TypeError) -> loop m_b_list in
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
       with Not_found -> raise (Error (NotStaticExp e)) in
     v
  | Elocal(n) ->
     let v =
       try Env.find n env with Not_found -> raise (Error(NotStaticExp e)) in v
  | Etuple(e_list) ->
     Global.value_code (Vtuple(List.map (expression env) e_list))
  | Econstr1(c, e_list) ->
      Global.value_code (Vconstr1(Modules.qualident c,
                                  List.map (expression env) e_list))
  | Erecord(n_e_list) -> 
     let v_exp =
       Vrecord(List.map
		 (fun (ln, e) -> (Modules.qualident ln, expression env e))
		 n_e_list) in
     Global.value_code v_exp
  | Erecord_with(e_record, n_e_list) -> 
     let { value_exp = v_exp } = expression env e_record in
     let n_v_list =
       List.map
	 (fun (ln, e) -> (Modules.qualident ln, expression env e)) n_e_list in
     let v_exp =
       match v_exp with
       | Vrecord(l_v_list) ->
	  Vrecord(List.map
		    (fun (ln, v) ->
		     (ln,
		      try
			List.assoc ln n_v_list
		      with
		      | Not_found -> v))
		    l_v_list)
       | _ -> raise (Error(TypeError)) in
     Global.value_code v_exp
  | Erecord_access(e_record, ln) ->
     record_access (expression env e_record) ln
  | Eop _ | Elast _ -> raise (Error (NotStaticExp e))
  | Eapp(_, e, e_list) ->
     let v = expression env e in
     let v_list = List.map (expression env) e_list in
     app v v_list
  | Etypeconstraint(e, _) -> expression env e
  | Eseq(e1, e2) ->
     ignore (expression env e1); expression env e2
  | Eperiod { p_phase = p1; p_period = p2 } ->
     Global.value_code
       (Vperiod { p_phase = Misc.optional_map (expression env) p1;
                  p_period = expression env p2 })
  | Elet(l, e_let) ->
     let env = local env l in
     expression env e_let
  | Eblock _ -> raise (Error (NotStaticExp e))
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
    | [], _ -> raise (Error(TypeError))
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
     let i = if op = Initial.stdlib_name "+" then i1 + i2
	     else if op = Initial.stdlib_name "-" then i1 - i2
	     else raise (Error(TypeError)) in
     value_code (Vconst(Eint(i)))
  | _ -> raise (Error(TypeError))

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
  | EQemit _ | EQautomaton _ | EQforall _ -> raise (Error(NotStaticEq eq))
						   
and block env { b_locals = l_list; b_body = eq_list } =
  let env = List.fold_left local env l_list in
  List.fold_left equation env eq_list
