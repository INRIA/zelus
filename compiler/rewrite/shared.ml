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

(* Identify assignments to shared variables and memories. *)
(* Applied on normalized expressions and equations *)

(* After this transformation, equations on structured patterns *)
(* like [pat = e] are such that no variable in [pat] *)
(* is shared nor a memory. All equations on those variables *)
(* are then of the form [x = e] *)

open Location
open Ident
open Zelus
open Deftypes
open Zaux

(* Computes the set of shared memories and state variables. *)
(* add them to [dv] *)
let shared dv l_env =
  let add x sort acc =
    match sort with | Sstatic | Sval -> acc | Svar _ | Smem _ -> S.add x acc in
  Env.fold (fun x { t_sort = sort } acc -> add x sort acc) l_env dv
    
(* Remove the flag [is_copy] from a environment of copies *)
let remove_is_copy copies =
  Env.map (fun (x_copy, _, ty) -> (x_copy, false, ty)) copies

(* Makes a list of copy equations [x = x_copy] for every entry in [env] *)
(* when the [is_copy] flag is true *)
let add_equations_for_copies eq_list copies =
  (* makes a value for [x_copy] *)
  Env.fold
    (fun x (x_copy, is_copy, ty) acc ->
     if is_copy then
       (eqmake (EQeq(varpat x ty, var x_copy ty))) :: acc
     else acc) copies eq_list

(* Extends the local environment with definitions for the [x_copy] *)
let add_locals_for_copies n_list n_env copies =
  let value ty = { t_sort = Deftypes.value; t_typ = ty } in
  let n_env =
    Env.fold
      (fun x (x_copy, _, ty) acc ->
       Env.add x_copy (value ty) acc) copies n_env in
  let n_copy_list =
    Env.fold
      (fun _ (x_copy, _, ty) acc ->
       (Zaux.vardec_from_entry x_copy { t_sort = Sval; t_typ = ty }) :: acc)
      copies n_list in
  n_copy_list, n_env

(* Makes a copy of a pattern if it contains a shared variable [x] *)
(* introduce auxilary equations [x = x_copy] in [copies] for every name *)
(* in [dv] *)
let rec pattern dv copies pat =
  match pat.p_desc with
  | Ewildpat | Econstpat _ | Econstr0pat _ -> pat, copies
  | Etuplepat(p_list) ->
      let p_list, copies = Misc.map_fold (pattern dv) copies p_list in
      { pat with p_desc = Etuplepat(p_list) }, copies
  | Econstr1pat(c, p_list) ->
      let p_list, copies = Misc.map_fold (pattern dv) copies p_list in
      { pat with p_desc = Econstr1pat(c, p_list) }, copies
  | Evarpat(n) -> 
      if S.mem n dv then
        let ncopy = Ident.fresh "copy" in
        { pat with p_desc = Evarpat(ncopy) },
	Env.add n (ncopy, true, pat.p_typ) copies
      else pat, copies
  | Erecordpat(label_pat_list) ->
      let label_pat_list, copies =
        Misc.map_fold
	  (fun copies (label, p) -> 
                 let p, copies = pattern dv copies p in
                 (label, p), copies) copies label_pat_list in
      { pat with p_desc = Erecordpat(label_pat_list) }, copies
  | Etypeconstraintpat(p, ty) ->
      let p, copies = pattern dv copies p in
      { pat with p_desc = Etypeconstraintpat(p, ty) }, copies
  | Ealiaspat(p, n) ->
      let p, copies = pattern dv copies p in
      let n, copies = 
        if S.mem n dv then
          let ncopy = Ident.fresh "copy" in
          ncopy, Env.add n (ncopy, true, p.p_typ) copies
        else n, copies in
      { pat with p_desc = Ealiaspat(p, n) }, copies
  | Eorpat _ -> assert false

(* [dv] is the set of names possibly written in [eq] which are visible *)
(* outside of the block or are memories *)
let rec equation dv copies ({ eq_desc = desc } as eq) =
  match desc with
    | EQeq({ p_desc = Evarpat(n) }, _) -> eq, copies
    | EQeq(pat, e) ->
       (* if some variable from [pat] are shared, [pat] is renamed into [pat'] *)
       (* and auxiliary equations [x1 = x_copy1 and ... and xn = x_copyn] *)
       (* are added *)
       let pat, copies = pattern dv copies pat in
       { eq with eq_desc = EQeq(pat, e) }, copies
    | EQpluseq _ | EQder _ | EQinit _ -> eq, copies
    | EQmatch(total, e, m_h_list) ->
       let m_h_list =
         List.map
	   (fun ({ m_body = b } as h) -> { h with m_body = block dv b } )
	   m_h_list in
       { eq with eq_desc = EQmatch(total, e, m_h_list) }, copies
    | EQreset(res_eq_list, e) ->
       let res_eq_list, copies = equation_list dv copies res_eq_list in
       { eq with eq_desc = EQreset(res_eq_list, e) }, copies
    | EQand(and_eq_list) ->
       let and_eq_list, copies = equation_list dv copies and_eq_list in
       { eq with eq_desc = EQand(and_eq_list) }, copies
    | EQbefore(before_eq_list) ->
       let before_eq_list, copies = equation_list dv copies before_eq_list in
       { eq with eq_desc = EQbefore(before_eq_list) }, copies
    | EQforall _ -> eq, copies
    | EQemit _ | EQautomaton _ | EQpresent _
    | EQnext _ | EQblock _ -> assert false
				     
(* [dv] defines names modified by [eq_list] but visible outside of the block *)
and equation_list dv copies eq_list = 
  let eq_list, copies_eq_list = Misc.map_fold (equation dv) Env.empty eq_list in
  let eq_list = add_equations_for_copies eq_list copies_eq_list in
  eq_list, Env.append (remove_is_copy copies_eq_list) copies
 
and local ({ l_eq = eq_list; l_env = l_env } as l) =
  let dv = shared S.empty l_env in
  let eq_list, copies = equation_list dv Env.empty eq_list in
  let _, l_env = add_locals_for_copies [] l_env copies in
  { l with l_eq = eq_list; l_env = l_env }
    
(* A variable [x] written by a block [b] is considered to be shared *)
(* when it is visible outside of the block, i.e., [x in dv_b] *)
(* Those variables and memories must be modified with equations of the *)
(* form [x = e] only. *)
and block dv ({ b_vars = n_list; b_body = eq_list; b_env = n_env;
		b_write = { dv = dv_b } } as b) =
  (* written variables [dv] are considered to be shared *)
  let dv = shared (S.union dv dv_b) n_env in
  let eq_list, copies = equation_list dv Env.empty eq_list in
  let n_list, n_env = add_locals_for_copies n_list n_env copies in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }

(* Expressions. *)
let exp ({ e_desc = desc } as e) =
  let desc =
    match desc with
    | Elet(l, e_let) -> Elet(local l, e_let)
    | _ -> desc in
  { e with e_desc = desc }
    
let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
  | Efundecl(n, ({ f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
