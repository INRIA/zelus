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

(* gather all horizons into a single one per function. Applied on *)
(* normalised expressions and equations *)

open Misc
open Ident
open Lident
open Deftypes
open Zelus
open Zaux
       
(* Compute the list of horizons and remove their kind in the environment *)
let gather_horizons env =
  let gather n ({ t_sort = sort } as entry) (h_list, env) =
    match sort with
    | Smem ({ m_kind = Some Horizon } as mem) ->
       n :: h_list,
       Env.add n { entry with t_sort = Smem { mem with m_kind = None } } env
    | _ -> h_list, Env.add n entry env in
  Env.fold gather env ([], Env.empty)

let horizon h_opt h_list eq_list =
  match h_list with
  | [] -> eq_list, h_opt
  | [x] ->
     let h = match h_opt with | None -> Ident.fresh "h" | Some(h) -> h in
     (pluseq_make h (float_var x)) :: eq_list, Some(h)
  | x :: l ->
     let h = match h_opt with | None -> Ident.fresh "h" | Some(h) -> h in
     let e =
       List.fold_left (fun acc y -> min_op acc (float_var y)) (float_var x) l in
     (pluseq_make h e) :: eq_list, Some(h)

(* Translation of equations. The function returns a new equation *)
(* and a possible horizon [h] *)
let rec equation h_opt ({ eq_desc = desc } as eq) =
  match desc with 
  | EQmatch(total, e, m_h_list) ->
     let m_h_list, h_opt =
       Misc.map_fold
	 (fun h_opt ({ m_body = b } as m_h) ->
	  let b, h_opt = block h_opt b in
	  { m_h with m_body = b }, h_opt) h_opt m_h_list in
     { eq with eq_desc = EQmatch(total, e, m_h_list) }, h_opt
  | EQreset(eq_list, e) ->
     let eq_list, h_opt = equation_list h_opt eq_list in
     { eq with eq_desc = EQreset(eq_list, e) }, h_opt
  | EQand(and_eq_list) ->
     let and_eq_list, h_opt = equation_list h_opt and_eq_list in
     { eq with eq_desc = EQand(and_eq_list) }, h_opt
  | EQbefore(before_eq_list) ->
     let before_eq_list, h_opt = equation_list h_opt before_eq_list in
     { eq with eq_desc = EQbefore(before_eq_list) }, h_opt
  | EQinit _ | EQder _ | EQeq _
  | EQpluseq _ -> eq, h_opt
  | EQforall ({ for_body = b_eq_list } as body) ->
     let b_eq_list, h_opt = block h_opt b_eq_list in
     { eq with eq_desc = EQforall { body with for_body = b_eq_list } }, h_opt
  | EQblock _ | EQautomaton _
  | EQpresent _ | EQemit _ | EQnext _ -> assert false

and equation_list h_opt eq_list = Misc.map_fold equation h_opt eq_list      

and equation_list_with_horizon h_opt n_env eq_list =
  let h_list, n_env = gather_horizons n_env in
  let eq_list, h_opt = equation_list h_opt eq_list in
  let eq_list, h_opt = horizon h_opt h_list eq_list in
  n_env, eq_list, h_opt
		    
(** Translate a block *)
and block h_opt ({ b_body = eq_list; b_env = n_env } as b) =
  let n_env, eq_list, h_opt = equation_list_with_horizon h_opt n_env eq_list in
  { b with b_body = eq_list; b_env = n_env }, h_opt
						
let expression ({ e_desc = desc } as e) =
  match desc with
  | Elet({ l_eq = eq_list; l_env = l_env } as l, e) ->
     let l_env, eq_list, h_opt =
       equation_list_with_horizon None l_env eq_list in
     let l, e =
       match h_opt with
       | None -> { l with l_eq = eq_list; l_env = l_env }, e
       | Some(h) ->
	  (* declaration of [h: float default infinity with (min)] *)
	 let sort =
	    Deftypes.default
	      (Some(Deftypes.Cglobal(Modname(Initial.stdlib_name
					       "infinity"))))
	      (Some(Modname(Initial.stdlib_name "min"))) in
	 let l_env =
	    Env.add h (Deftypes.entry sort Initial.typ_float) l_env in
	 let hor = Ident.fresh "h" in
	 let sort = Deftypes.horizon Deftypes.empty_mem in
	 let l_env =
	   Env.add hor (Deftypes.entry sort Initial.typ_float) l_env in
	 let eq_list =
	   Zaux.eq_make hor (Zaux.var h Initial.typ_float) :: eq_list in
	 { l with l_eq = eq_list; l_env = l_env }, e in
     { e with e_desc = Elet(l, e) }
  | _ -> e
	   
let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl(_, { f_kind = (S | A | AS | AD | D | P) }) -> impl
  | Efundecl(n, ({ f_kind = C; f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = expression e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
