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

(* rewrite of an [der x = e init e0 reset z1 -> e1 | ... | zn -> en] *)
(* into [present z1 -> x = e1 | ...  and init x = e0 and der x = e] *)

open Location
open Zelus

(* turns [z1 -> e1|...|zn -> en] into [z1 -> id = e1|...|id = en] *)
let p_handlers id handlers =
  List.map 
    (fun { p_cond; p_body = e; p_zero; p_env; p_loc } ->
      { p_cond; p_zero; p_env; p_loc; p_body = Aux.id_eq id e })
  handlers

let present_der id e0_opt handlers eq =
  let eq = match handlers with
    | [] -> eq
    | _ ->
       let handlers = p_handlers id handlers in
       Aux.eq_and
         (Aux.eqmake (Defnames.singleton id)
            (EQpresent { handlers; default_opt = NoDefault })) eq in
  match e0_opt with
  | None -> eq | Some(e0) -> Aux.eq_and eq (Aux.eq_init id e0)

let equation funs acc eq =
  let { eq_desc } as eq, acc = Mapfold.equation funs acc eq in
  match eq_desc with
  | EQder { e_opt = None; handlers = [] } ->
     eq, acc
  | EQder { id; e; e_opt; handlers } -> 
     let eq = present_der id e_opt handlers (Aux.eq_der id e) in
       eq, acc
  | _ -> raise Mapfold.Fallback

let program genv0 p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; global_funs } in
  let p, _ = Mapfold.program_it funs genv0 p in
  p
