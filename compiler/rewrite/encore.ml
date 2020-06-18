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

(* applied to normalised equations and expressions *)
(* add of an horizon [h = if encore then 0.0 else infinity] to *)
(* every function body and the declaration of a variable [encore] *)
(* with default value [false] *)
(* An equation [encore = true] is added in a block activated on *)
(* a zero-crossing and which writes a non local state variable *)
(* match e with | P1 -> (* zero *) x = ... | Pn -> ... *)
(* into:  match e with | P1 -> do encore = true and x = ... | ... *)

open Misc
open Location
open Ident
open Lident
open Initial
open Deftypes
open Zelus
open Zaux
	 
(* Does the block contains an equation [x = e] on a last variable? *)
let encore env { dv = dv } =
  let write_on_last x =
    let { t_sort = sort } =
      try Env.find x env
      with Not_found ->
	Misc.internal_error "Encore: unbound name" Printer.name x in
      match sort with
      | Smem { m_previous = previous } -> previous | _ -> false in
  S.exists write_on_last dv

(** Add an equation [encore = true] *)
let with_zero env encore_opt ({ b_body = eq_list; b_write = w } as b) =
  if encore env w then
    let encore =
      match encore_opt with
	| None -> Ident.fresh "encore" | Some(encore) -> encore in
    { b with b_body = (Zaux.eq_make encore Zaux.etrue) :: eq_list }, Some(encore)
  else b, encore_opt
    
(* Translation of equations *)
let rec equation env encore_opt ({ eq_desc = desc } as eq) =
  match desc with 
    | EQeq _ | EQpluseq _ | EQder _ | EQinit _ -> eq, encore_opt
    | EQreset(eq_list, e) ->
       let eq_list, encore_opt = equation_list env encore_opt eq_list in
       { eq with eq_desc = EQreset(eq_list, e) }, encore_opt
    | EQand(and_eq_list) ->
       let and_eq_list, encore_opt = equation_list env encore_opt and_eq_list in
       { eq with eq_desc = EQand(and_eq_list) }, encore_opt
    | EQbefore(before_eq_list) ->
       let before_eq_list, encore_opt =
	 equation_list env encore_opt before_eq_list in
       { eq with eq_desc = EQbefore(before_eq_list) }, encore_opt
    | EQmatch(total, e, m_h_list) ->
     (* add an equation [encore = true] if a branch is activated *)
     (* on a zero-crossing and changes a non local state variable *)
     (* whose last value is read outside *)
      let m_h_list, encore_opt =
	Misc.map_fold
	  (fun encore_opt ({ m_zero = zero; m_body = b } as m_h) ->
	    let b, encore_opt =
	      if zero then with_zero env encore_opt b
	      else block env encore_opt b in
	    { m_h with m_body = b }, encore_opt)
	  encore_opt m_h_list in
      { eq with eq_desc = EQmatch(total, e, m_h_list) }, encore_opt
    | EQforall ({ for_body = b_eq_list } as body) ->
       let b_eq_list, encore_opt = block env encore_opt b_eq_list in
       { eq with eq_desc = EQforall { body with for_body = b_eq_list }},
       encore_opt
    | EQautomaton _ | EQpresent _ | EQemit _
    | EQnext _ | EQblock _ -> assert false

and equation_list env encore_opt eq_list =
  Misc.map_fold (equation env) encore_opt eq_list      

(** Translate a block *)
and block env encore_opt ({ b_body = eq_list; b_env = n_env } as b) =
  let env = Env.append n_env env in
  let eq_list, encore_opt = equation_list env encore_opt eq_list in
  { b with b_body = eq_list }, encore_opt

(** Translate an expression. Add two declarations if an extra step *)
(** is needed. [encore] is a local variable with default value [false]; *)
(** [h] is an horizon such that [h = if encore then 0.0 else infinity] *)
let expression env ({ e_desc = desc } as e) =
  match desc with
  | Elet({ l_eq = eq_list; l_env = l_env } as l, e) ->
    let env = Env.append l_env env in
    let eq_list, encore_opt = equation_list env None eq_list in
     let l =
       match encore_opt with
       | None -> { l with l_eq = eq_list; l_env = l_env }
       | Some(encore) ->
	 (* declaration of [encore: bool default false] *)
	 let sort =
	   Deftypes.default
	     (Some(Deftypes.Cimmediate(Deftypes.Ebool(false)))) None in
	  let l_env =
	    Env.add encore (Deftypes.entry sort Initial.typ_bool) l_env in
	  (* declaration of [horizon h] *)
	  let h = Ident.fresh "h" in
	  let sort = Deftypes.horizon Deftypes.empty_mem in
	  let l_env =
	    Env.add h (Deftypes.entry sort Initial.typ_float) l_env in
	  (* add equation [h = if encore then 0.0 else infinity] *)
	  let eq_list =
	    Zaux.eq_make h (ifthenelse (Zaux.var encore Initial.typ_bool)
			      Zaux.zero Zaux.infinity) :: eq_list in
	  { l with l_eq = eq_list; l_env = l_env } in
     { e with e_desc = Elet(l, e) }
  | _ -> e
    
let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl(_, { f_kind = (S | AS | A | AD | D | P) }) -> impl
  | Efundecl(n, ({ f_kind = C; f_body = e; f_env = f_env } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = expression f_env e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
