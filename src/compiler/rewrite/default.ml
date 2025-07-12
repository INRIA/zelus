(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* propagate the default value and initialisation into the body of a block *)
(* E.g., [local x default e,... do eq] and [local x init e,... do eq *)
(* match e with P1 -> x = ... | P2 -> y = ...] is rewritten *)
(* match e with P1 -> x = ... and y = def_y | P2 -> y = ... and x = def_x] *)
(* [def_y] is the default value if defined; last y otherwise *)
(* this step also replace [local ... do eq in e] by [let rec eq in e] *)
open Zelus
open Ident
open Defnames
open Aux
open Mapfold

(* The accumulator [acc] is an environment of default values [name -> exp] *)
let block funs acc ({ b_vars; b_body; b_write; b_env } as b) =
  let vardec
        (init_list, acc)
        ({ var_name; var_default; var_init; var_init_in_eq } as v) =
    let acc =
      match var_default with
      | None -> acc
      | Some(e) ->
         let e, _ = Mapfold.expression_it funs acc e in
         Env.add var_name e acc in
    let var_init_in_eq, init_list =
      match var_init with
      | None -> var_init_in_eq, init_list
      | Some(e) ->
         let e, _ = Mapfold.expression_it funs acc e in
         true, (Aux.eq_init var_name e) :: init_list in
    { v with var_default = None; var_init = None; var_init_in_eq },
    (init_list, acc) in
  let b_vars, (init_list, acc) =
    Util.mapfold vardec ([], acc) b_vars in
  let b_body, _ =
    Mapfold.equation_it funs acc b_body in
  { b with b_vars; b_body = Aux.par (b_body :: init_list) }, acc

(* for a by-case definition, complete the branch where [x] has no definition *)
(* by its default one when it exists *)
let complete acc { dv = dv_global} ({ eq_desc; eq_write } as eq) =
  let l = S.diff dv_global eq_write.dv in
  let eq_list =
    S.fold
      (fun x eq_list ->
        (* if [acc(x) exists, add equation [x = acc(x)] *)
        try Aux.id_eq x (Env.find x acc) :: eq_list
        with Not_found -> eq_list)
      l [eq] in
  Aux.par eq_list

let expression funs acc e =
  let ({ e_desc } as e), _ = Mapfold.expression funs acc e in
  match e_desc with
  | Elocal({ b_body; b_loc }, e_local) ->
     { e with e_desc = Elet(Aux.leq [b_body], e_local) }, acc
  | _ -> e, acc

let equation funs acc eq =
  let { eq_desc; eq_write } as eq, _ = Mapfold.equation funs acc eq in
  match eq_desc with
  | EQif { e; eq_true; eq_false } ->
     let eq_true = complete acc eq_write eq_true in
     let eq_false = complete acc eq_write eq_false in
     { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
  | EQmatch({ is_size; is_total; e; handlers } as m) ->
     let handler ({ m_body } as m_h) =
       let m_body = complete acc eq_write m_body in
       { m_h with m_body } in
     let handlers = List.map handler handlers in
     if is_total then
       { eq with eq_desc = EQmatch { m with e; handlers } }, acc
     else
        (* add a handler [_ -> default_eq] when the pattern matching is partial *)
       (* [default_eq] is a list of  default equations for *)
       (* variables in [eq_write] *)
        let m_body = complete acc eq_write (Aux.eq_empty ()) in
        let m_h =
          { m_pat = Aux.wildpat; m_loc = Location.no_location;
            m_reset = false; m_zero = false; m_env = Env.empty;
            m_body } in
        { eq with eq_desc = EQmatch { is_size; is_total = true; e;
                                      handlers = handlers @ [m_h] } }, acc
  | _ -> eq, acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with block; expression; equation; global_funs } in
  let p, _ = Mapfold.program_it funs Env.empty p in
  p
