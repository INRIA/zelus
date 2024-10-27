(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Elimination of atomic values copy variables [x = y], constants, globals *)
(* The transformation is applied after static scheduling and before *)
(* translation into sequential code *)

open Misc
open Ident
open Zelus
open Deftypes

(** atomic expressions - either immediate constants or variables *)
type 'a value = | Vvar of Ident.t | Vlast of Zelus.last | Vconst of 'a
						    
type 'a renaming =
    { rel: 'a Env.t; (* the substitution *)
      defs: S.t; (* names for which the substitution cannot be applied *)
    }

let empty = { rel = Env.empty; defs = S.empty }

(** Append a renaming with a new relation *)
let append new_rel ({ rel } as renaming) =
  { renaming with rel = Env.append new_rel rel }
    
(* Apply the renaming recursively. If [rel = [n\n1, n1\n2]], then *)
(* [rename n rel] = n2 *)
(* A substitution [n\last m] is not performed when [m] belongs to [defs] *)
let rename n { rel; defs } =
  let rec rename n =
    try 
      let m = Env.find n rel in
      begin
	match m with
	| Vvar m -> rename m
	| Vlast({ id } as l) ->
           if S.mem id defs then raise Not_found else Elast l
	| Vconst(v) -> v
      end
    with Not_found -> Evar n in
  rename n

let rec size ({ rel } as renaming) ({ desc } as s) =
  try
    let s =
      match desc with
      | Size_int _ -> s
      | Size_var(n) ->
         let n = Env.find n rel in
         begin match n with
         | Vvar n -> { s with desc = Size_var(n) }
         | _ -> raise Not_found
         end
      | Size_op(op, s1, s2) ->
         { s with desc = Size_op(op, size renaming s1, size renaming s2) }
      | Size_frac({ num } as f) ->
         { s with desc = Size_frac({ f with num = size renaming num }) } in
    s
  with
    Not_found -> s

(* Build a substitution [x1\v1,...,xn\vn] *)
let rec build rel { eq_desc } =
  match eq_desc with
  | EQeq({ pat_desc = Evarpat(x) }, { e_desc }) ->
     let rel =
       match e_desc with
       | Evar m -> Env.add x (Vvar(m)) rel
       | Eglobal _ | Econst _ -> Env.add x (Vconst(e_desc)) rel
       | Elast m -> Env.add x (Vlast(m)) rel
       | _ -> rel in
     rel
  | EQreset(eq, _) -> build rel eq
  | EQand { eq_list } -> List.fold_left build rel eq_list
  | _ -> rel

(* Function to traverse the ast *)
(* Apply [renaming] to every sub-expression *)
let expression funs renaming ({ e_desc } as e) =
  match e_desc with
  | Evar(id) -> { e with e_desc = rename id renaming }, renaming
  | _ -> raise Mapfold.Fallback
						
(* Local declarations *)
let leq_t funs renaming ({ l_eq } as l) =
  let rel = build Env.empty l_eq in
  let new_renaming = append rel renaming in
  let l_eq, renaming = Mapfold.equation_it funs new_renaming l_eq in
  { l with l_eq }, renaming

let block funs renaming ({ b_body } as b) =
  let rel = build Env.empty b_body in
  let new_renaming = append rel renaming in
  let b_body, renaming = Mapfold.equation_it funs new_renaming b_body in
  { b with b_body }, renaming

let program genv p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with
      expression; leq_t; block; global_funs } in
  let p, _ = Mapfold.program_it funs empty p in
  p
