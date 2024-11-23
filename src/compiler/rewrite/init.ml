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

(* removes the initialization operator [e1 -> e2] and normalize *)
(* initialization equations [init x = e] *)
(* Requires that all initializations of blocks declarations *)
(* have been moved into the body *)

open Misc
open Location
open Ident
open Zelus
open Mapfold

(*
  [e1 -> e2] is rewritten in [if last* i then e1 else e2]

  if [i] is the initialization bit of the current block
  
  [init x = e] (* [e] is static *) is left unchanged.

  [init x = e ... (* [e] is not static *) is rewritten:

  [reset init x = e every last* i]
   
   for every control block, introduce an initialization bit. E.g.,:

   [match e with
   | P1 -> eq1 | ... | Pn -> eqn]

   is rewritten:

   [match e with
   | P1 -> local i1 do init i1 = true and i1 = false and eq1
   | ...
   | Pn -> local in do init in = true and in = false and eqn]
*)

let fresh () = Ident.fresh "i"

(* the initialization variable *)
type acc = { i : Ident.t option }

let empty = { i = None }

let intro { i } =
  let id = match i with | None -> fresh () | Some(id) -> id in
  id, { i = Some(id) }

(* [e1 -> e2] translated into [if id then e1 else e2] *)
let ifthenelse acc e1 e2 =
  let id, acc = intro acc in
  Aux.emake (Eop(Eifthenelse, [Aux.last_star id; e1; e2])), acc

(* Surround an equation [eq] by a reset, that is, generate *)
(* [reset eq every last* id] *)
let reset_init acc eq =
  let id, acc = intro acc in
  Aux.eq_reset eq (Aux.last_star id), acc

let init id = [Aux.id_eq id Aux.efalse; Aux.eq_init id Aux.etrue]

(* [local id do init id = true and id = false and eq done] *)
let local_init_in_eq { i } eq =
  match i with
  | None -> eq
  | Some(id) ->
     Aux.eq_local
       (Aux.block_make [Aux.vardec id false None None] (eq :: (init id)))

(* [let rec init id = true and id = false in e] *)
let let_init_in_exp { i } e =
  match i with
  | None -> e | Some(id) -> Aux.e_letrec (init id) e

(* all the constructs below are atomic blocks, that is, *)
(* a fresh initialization variable is necessary *)
let atomic_eq funs acc eq =
  let eq, acc_local = Mapfold.equation_it funs empty eq in
  local_init_in_eq acc_local eq, acc

let atomic_exp funs acc e =
  let e, acc_local = Mapfold.expression_it funs empty e in
  let_init_in_exp acc_local e, acc

let leq_t funs acc ({ l_eq } as l) =
  let l_eq, { i } = Mapfold.equation_it funs empty l_eq in
  match i with
  | None -> { l with l_eq }, acc
  | Some(id) -> { l with l_eq = Aux.par (l_eq :: init id) }, acc

(* this step is done after the initialization and default part have been *)
(* moved into the body *)
let block funs acc ({ b_vars; b_body } as b) =
  let b_body, { i } = Mapfold.equation_it funs empty b_body in
  match i with
  | None -> { b with b_body }, acc
  | Some(id) ->
     { b with b_vars = Aux.id_vardec id :: b_vars;
              b_body = Aux.par (b_body :: init id) }, acc

let reset_eq funs acc eq = atomic_eq funs acc eq
let reset_e funs acc e = atomic_exp funs acc e

let match_handler_eq funs acc ({ m_body } as m_h) =
  let m_body, acc = Mapfold.reset_eq funs acc m_body in 
  { m_h with m_body }, acc

let match_handler_eq funs acc ({ m_body } as m_h) =
  let m_body, acc = reset_eq funs acc m_body in 
  { m_h with m_body }, acc

and if_eq funs acc (eq_true, eq_false) =
  let eq_true, acc = Mapfold.reset_eq funs acc eq_true in
  let eq_false, acc = Mapfold.reset_eq funs acc eq_false in
  (eq_true, eq_false), acc

(* Equations *)
let equation funs acc ({ eq_desc } as eq) =
  match eq_desc with
  | EQinit(_, e) when Types.static e -> eq, acc
  | EQinit(x, e) ->
     let e, acc = Mapfold.expression_it funs acc e in
     reset_init acc { eq with eq_desc = EQinit(x, e) }
  | _ -> raise Mapfold.Fallback

(* Expressions. *)
let expression funs acc e =
  let { e_desc } as e, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Eop(Eminusgreater, [e1; e2]) ->
     (* [if last i then e1 else e2] *)
     ifthenelse acc e1 e2
  | _ -> e, acc

let result funs acc ({ r_desc } as r) =
  (* introduce one init per branch *)
  let r_desc, acc = match r_desc with
    | Exp(e) ->
       let e, acc = Mapfold.reset_e funs acc e in
       Exp(e), acc
    | Returns(b) ->
       let b, acc = Mapfold.block funs acc b in
       Returns(b), acc in
  { r with r_desc }, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with leq_t; block; expression; equation; result;
                            reset_eq; reset_e; match_handler_eq;
                            if_eq; set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

