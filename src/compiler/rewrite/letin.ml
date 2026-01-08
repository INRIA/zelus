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

(* Remove nested declaration of variables *)
(* Preserves the sequential order defined by let/in *)
(* declarations. If side-effects or unsafe functions appear, their *)
(* order given by the let/in is preserved *)
(* E.g., in [let x = e1 in e2], all side effects in [e1] are done before *)
(* those of [e2] *)
(* [let x = e1 in e2] has the behavior of [let x = e1 andthen y = e2 in y] *)

(* Assume that default and init values have been propagated into equations *)
(* and are no more at the declaration point *)
(* Invariant: an expression is normalized into a pair [(vardec_list, eq), e] *)
(* whose meaning is [local vardec do eq in e] *)
(* An equation is normalized into [local vardec do eq] *)

open Misc
open Location
open Ident
open Zelus
open Aux
open Parseq

(* a structure to represent nested equations before they are turned into *)
(* Zelus equations *)
type ('info, 'env) acc =
  { c_vardec: ('info, ('info, 'env) exp) vardec list Parseq.t;
    c_eq: ('info, 'env) eq Parseq.t }

let empty = { c_vardec = Parseq.Empty; c_eq = Parseq.Empty }

let empty_eq = eqmake Defnames.empty EQempty

let par { c_vardec = v1; c_eq = c_eq1 } { c_vardec = v2; c_eq = c_eq2 } =
  { c_vardec = Parseq.par v1 v2; c_eq = Parseq.par c_eq1 c_eq2 }
let seq { c_vardec = v1; c_eq = c_eq1 } { c_vardec = v2; c_eq = c_eq2 } =
  { c_vardec = Parseq.seq v1 v2; c_eq = Parseq.seq c_eq1 c_eq2 }
let add_seq eq ({ c_eq } as ctx) =
  { ctx with c_eq = Parseq.seq (Parseq.singleton eq) c_eq }
let add_par eq ({ c_eq } as ctx) =
  { ctx with c_eq = Parseq.par (Parseq.singleton eq) c_eq }
let add_vardec vardec_list ({ c_vardec } as ctx) =
  { ctx with c_vardec = Parseq.Cons(vardec_list, c_vardec) }
let add_names n_names ctx =
  let vardec_list = S.fold (fun id acc -> Aux.id_vardec id :: acc) n_names [] in
  add_vardec vardec_list ctx
				   				      
(* translate a context [acc] into an environment and an equation *)
let equations eqs =
  (* computes the set of sequential equations *)
  let rec seq eqs eq_list =
    match eqs with
    | Parseq.Empty -> eq_list
    | Parseq.Cons(eq, eqs) -> eq :: seq eqs eq_list
    | Parseq.Seq(eqs1, eqs2) ->
       seq eqs1 (seq eqs2 eq_list)
    | Parseq.Par(eqs1, eqs2) ->
       let par_eq_list = par [] eqs1 in
       let par_eq_list = par par_eq_list eqs2 in
       Aux.par par_eq_list :: eq_list
  (* and the set of parallel equations *)
  and par eq_list eqs =
    match eqs with
    | Parseq.Empty -> eq_list
    | Parseq.Cons(eq, eqs) -> par (eq :: eq_list) eqs
    | Parseq.Seq(eqs1, eqs2) ->
       let seq_eq_list = seq eqs2 [] in
       let seq_eq_list = seq eqs1 seq_eq_list in
       Aux.seq seq_eq_list :: eq_list
    | Parseq.Par(eqs1, eqs2) ->
       par (par eq_list eqs1) eqs2 in
  par [] eqs

let vardec_list_eq { c_vardec; c_eq } =
  let vardec_list = Parseq.fold (@) c_vardec [] in
  let eq_list = equations c_eq in
  vardec_list, eq_list

(* build an equation [local vardec_list do eq done] from [acc] *)
let eq_local acc =
  let vardec_list, eq_list = vardec_list_eq acc in
  Aux.eq_local_vardec vardec_list eq_list     

let e_local acc e =
  let vardec_list, eq_list = vardec_list_eq acc in
  Aux.local_vardec_in_e vardec_list eq_list e

let pattern funs acc p = p, acc

let atomic_expression funs acc e =
  let e, acc = Mapfold.expression_it funs acc e in
  e_local acc e

(* Translation of expressions *)
(* [expression funs { c_vardec; c_eq } e = [e', { c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq in e] and *)
(* [local c_vardec' do c_eq' in e'] are equivalent *)
let expression funs acc ({ e_desc } as e) =
  let e, acc_e = match e_desc with
    | Eop(Eseq, [e1; e2]) ->
       (* the sequential order is preserved *)
       (* [e1; e2] is a short-cut for [let _ = e1 in e2] *)
       let e1, acc_e1 = Mapfold.expression_it funs empty e1 in
       let e2, acc_e2 = Mapfold.expression_it funs empty e2 in
       e2, seq acc_e1 (add_seq (Aux.wildpat_eq e1) acc_e2)
    | Elet(l, e) ->
       (* the sequential order is preserved *)
       let _, acc_l = Mapfold.leq_it funs empty l in
       let e, acc_e = Mapfold.expression_it funs empty e in
       e, seq acc_l acc_e
    | Elocal({ b_vars; b_body }, e) ->
       (* the sequential order is preserved *)
       (* [b_vars] does not contain expressions (default/init) anymore *)
       let _, acc_b = Mapfold.equation_it funs empty b_body in
       let e, acc_e = Mapfold.expression_it funs empty e in
       e, add_vardec b_vars (seq acc_b acc_e)
    | Eassert({ a_body } as a) ->
       let a_body, acc =
         if !Misc.transparent then atomic_expression funs empty a_body, empty
         else Mapfold.expression_it funs empty a_body in
       { e with e_desc = Eassert { a with a_body } }, acc
    | _ ->
       Mapfold.expression funs empty e in
  let acc_e = par acc acc_e in
  e, acc_e

let atomic_equation funs acc eq =
  let eq, acc = Mapfold.equation_it funs acc eq in
  eq_local acc

(* Translate an equation. *)
(* [equation funs { c_vardec; c_eq } eq = empty_eq, [{ c_vardec'; c_eq'}] *)
(* such that [local c_vardec do c_eq and eq] and *)
(* [local c_vardec' do c_eq'] are equivalent *)
let equation funs acc ({ eq_desc } as eq) =
  let acc_eq = match eq_desc with 
    | EQand { eq_list } ->
       let _, acc = Util.mapfold (Mapfold.equation_it funs) empty eq_list in
       acc
    | EQinit(id, e_init) ->
       let e_init = atomic_expression funs empty e_init in
       add_par { eq with eq_desc = EQinit(id, e_init) } empty
    | EQlet(l, eq) ->
       (* definitions in [l] are merged with equations in [eq] *)
       (* but sequential order between them is preserved *)
       let _, acc_l = Mapfold.leq_it funs empty l in
       let _, acc_eq = Mapfold.equation_it funs empty eq in
       seq acc_l acc_eq
    | EQlocal { b_vars; b_body } ->
       (* [b_vars] does not contain expressions (default/init) anymore *)
       let _, acc_body = Mapfold.equation_it funs empty b_body in
       add_vardec b_vars acc_body
    | EQreset(eq_reset, e_reset) ->
       (* [reset local x1,... in eq every e] =
             [local x1,... in reset eq every e] *)
       let e_reset, acc_e_reset = Mapfold.expression_it funs empty e_reset in
       let _, { c_vardec; c_eq } = Mapfold.equation_it funs empty eq_reset in
       add_par { eq with eq_desc = EQreset(Aux.par (equations c_eq), e_reset) }
         (par acc_e_reset { c_vardec; c_eq = Parseq.Empty })
    | EQassert({ a_body } as a) ->
       let a_body, acc =
         if !Misc.transparent then atomic_expression funs empty a_body, acc
         else Mapfold.expression_it funs acc a_body in
       add_par
           { eq with eq_desc = EQassert { a with a_body } } acc
    | _ ->
       let eq, acc_eq = Mapfold.equation funs empty eq in
       seq acc_eq (add_seq eq empty) in
  empty_eq, par acc acc_eq

let leq_t funs acc ({ l_eq = { eq_write } as l_eq } as l) =
  let l_eq, acc = Mapfold.equation_it funs acc l_eq in
  let n_names = Defnames.names S.empty eq_write in
  { l with l_eq }, add_names n_names acc

let if_eq funs acc (eq_true, eq_false) =
  let eq_true = atomic_equation funs empty eq_true in
  let eq_false = atomic_equation funs empty eq_false in
  (eq_true, eq_false), acc

let match_handler_eq funs acc ({ m_body } as m_h) =
  let eq = atomic_equation funs empty m_body in
  { m_h with m_body = eq }, acc

let match_handler_e funs acc ({ m_body } as m_h) =
  let e = atomic_expression funs empty m_body in 
  { m_h with m_body = e }, acc

let present_handler_eq funs acc ({ p_cond; p_body } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body = atomic_equation funs empty p_body in
  { p_b with p_cond; p_body }, acc

let present_handler_e funs acc ({ p_cond; p_body } as p_b) =
  let p_cond, acc = Mapfold.scondpat_it funs acc p_cond in
  let p_body = atomic_expression funs empty p_body in
  { p_b with p_cond; p_body }, acc

let reset_e funs acc e = 
  let e = atomic_expression funs empty e in
  e, acc

let reset_eq funs acc eq = 
  let eq = atomic_equation funs empty eq in
  eq, acc

let result funs acc ({ r_desc } as r) =
  let r_desc = match r_desc with
  | Exp(e) ->
     let e = atomic_expression funs empty e in
     Exp(e)
  | Returns({ b_body } as b) ->
     (* assume that [b_vars] does not contain expressions (default/init) anymore *)
     let _, acc = Mapfold.equation_it funs empty b_body in
     Returns { b with b_body = eq_local acc } in
  { r with r_desc }, acc

let for_exp_t funs acc for_body =
  match for_body with
  | Forexp { exp; default } ->
     let exp = atomic_expression funs empty exp in
     let default =
       Util.optional_map (atomic_expression funs empty) default in
     Forexp { exp; default }, acc
  | Forreturns(f) ->
     let f, acc = Mapfold.for_returns_it funs acc f in
     Forreturns f, acc

let for_eq_t funs acc ({ for_out; for_block } as for_eq) =
  let for_out, _ =
    Util.mapfold (Mapfold.for_out_it funs) empty for_out in
  let for_block, _ = Mapfold.block_it funs empty for_block in
  { for_eq with for_out; for_block }, acc

let for_out_t funs acc ({ desc = ({ for_init; for_default } as desc) } as f) =
  let for_init =
    Util.optional_map (atomic_expression funs empty) for_init in
  let for_default =
    Util.optional_map (atomic_expression funs empty) for_default in
  { f with desc = { desc with for_init; for_default } }, acc

let letdecl funs acc (d_names, ({ l_eq } as leq)) =
  let _, acc_local = Mapfold.equation_it funs empty l_eq in
  (d_names, { leq with l_eq = eq_local acc_local }), acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with pattern; expression; equation; leq_t; 
                            if_eq; match_handler_eq; match_handler_e;
                            present_handler_eq; present_handler_e;
                            reset_e; reset_eq; result;
                            for_exp_t; for_eq_t; for_out_t;
                            letdecl; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }
