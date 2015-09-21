(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* add of an horizon [h = if encore then 0.0 else infinity] to *)
(* every function body. [encore] is a global boolean variable *)
(* to every function body such that: *)

(* the default value is [encore = false] *)
(* [encore = true] when an equation [x = e] on a last variable [x] *)
(* appears inside a condition that is activated on a zero-crossing event *)
(* match e with | P1 -> (* zero *) x = ... | Pn -> ... *)
(* into:  match e with *)
(*        | P1 -> do encore = true and x = ... | ... *)

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
	Misc.internal_error "Period: unbound name" Printer.name x in
      match sort with
      | Smem { m_previous = previous } -> previous | _ -> false in
  S.exists write_on_last dv

(* creates a block [local [horizon] h in eq] *)
let block_with_horizon h eq =
  let horizon = Deftypes.horizon Deftypes.empty_mem in
  make_block (Env.singleton h (Deftypes.entry horizon Initial.typ_float)) [eq]

(** Translation of expressions. *)
let rec expression env ({ e_desc = e_desc } as e) =
  match e_desc with

  | Elet(l, e) ->
       { e with e_desc = Elet(local env l, expression env e) }
    | Eapp(op, e_list) ->
       { e with e_desc = Eapp(op, List.map (expression env) e_list) }
    | Etuple(e_list) ->
       { e with e_desc = Etuple(List.map (expression env) e_list) }
    | Erecord_access(e, x) ->
       { e with e_desc = Erecord_access(expression env e, x) }
    | Erecord(l_e_list) ->
       let l_e_list = List.map (fun (l, e) -> (l, expression env e)) l_e_list in
       { e with e_desc = Erecord(l_e_list) }
    | Etypeconstraint(e, ty) ->
       { e with e_desc = Etypeconstraint(expression env e, ty) }
    | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e
    | Eseq(e1, e2) ->
       { e with e_desc = Eseq(expression env e1, expression env e2) }
    | Eperiod _ | Epresent _ | Ematch _ -> assert false

(* Translation of equations *)
and equation env ({ eq_desc = desc } as eq) =
  match desc with 
  | EQeq(p, e) -> { eq with eq_desc = EQeq(p, expression env e) }
  | EQmatch(total, e, m_h_list) ->
     let e = expression env e in
     (* does-it exist a branch which is executed on a zero-crossing instant? *)
     let zero = List.exists (fun { m_zero = zero; } -> zero) m_h_list in
     if zero then
       (* if this is the case, introduce the local variable [h] *)
       let h = Ident.fresh "h" in
       let m_h_list =
	 List.map
	   (fun ({ m_body = b; m_env = m_env; m_zero = zero } as m_h) ->
	    let env = Env.append m_env env in
	    { m_h with m_body = with_zero env zero h (block env b) }) m_h_list in
       let eq = { eq with eq_desc =
			    EQmatch(total, after e (float_last h), m_h_list) } in
       { eq with eq_desc = EQblock(block_with_horizon h eq) }
     else
       let m_h_list =
	 List.map
	   (fun ({ m_body = b; m_env = m_env } as m_h) ->
	    { m_h with m_body = block (Env.append m_env env) b }) m_h_list in
       { eq with eq_desc = EQmatch(total, e, m_h_list) }
  | EQblock(b) -> { eq with eq_desc = EQblock(block env b) }
  | EQreset(res_eq_list, e) ->
     let e = expression env e in
     { eq with eq_desc = EQreset(equation_list env res_eq_list, e) }
  | EQset(id, e) ->
     { eq with eq_desc = EQset(id, expression env e) }
  | EQinit(x, e) ->
     { eq with eq_desc = EQinit(x, expression env e) }
  | EQder(x, e, None, []) -> 
     { eq with eq_desc = EQder(x, expression env e, None, []) }
  | EQautomaton _ | EQpresent _ | EQemit _ | EQnext _ | EQder _ -> assert false

and equation_list env eq_list = List.map (equation env) eq_list      

(** Translate a block *)
and block env ({ b_locals = l_list; b_body = eq_list; b_env = n_env } as b) =
  let env = Env.append n_env env in
  let l_list = List.map (local env) l_list in
  let eq_list = equation_list env eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and local env ({ l_eq = eq_list; l_env = l_env } as l) =
  let env = Env.append l_env env in
  let eq_list = equation_list env eq_list in
  { l with l_eq = eq_list }

(* Add an encore step with [h = 0.0] for a block that is activated on *)
(* a zero-crossing instant and writes a discrete state variable [x] *)
(* [h = infinity] otherwise *)
and with_zero env zero h ({ b_body = eq_list; b_write = w } as b) =
  let eq = if zero && (encore env w) then eq_make h Zaux.zero
	   else eq_make h Zaux.infinity in
  { b with b_body = eq :: eq_list }

let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _  
  | Efundecl(_, { f_kind = (A | AD | D) }) -> impl
  | Efundecl(n, ({ f_kind = C; f_body = e; f_env = f_env } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = expression f_env e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
