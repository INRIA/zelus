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

(* dead-code removal. Applied to normalized code *)

open Misc
open Ident
open Vars
open Zelus
open Defnames
open Deftypes

(* def-use chains and useful variables *)
(* - the output variables of a function are useful. *)
(* - if [op] is an unsafe function (e.g., with side effects) *)
(*   in equation [y,... = op(x,...)], then [y,...] are useful *)
(* - if [x in write(eq) /\ useful(x) /\ y in read(eq)] then [useful(y)] *)
(* - if [x in write(eq) and [unsafe(eq)] then [useful(x)] *)
(* equations that define unreachable (non useful) variables are removed *)

type acc =
  { def_use: def_use_table; (* [y depends on x] *)
    read: S.t; (* a minimal subset of variables that need to be computed *)
  }

and def_use_table = cont Env.t

and cont = 
   { mutable c_vars: S.t; (* set of variables *)
     mutable c_useful: bool; (* is-it a useful variable? *)
     mutable c_visited: bool; (* has it been visited already? *)
   }

let empty = { def_use = Env.empty; read = S.empty }

(* Visit the table: recursively mark all useful variables *)
(* returns the set of useful variables *)
(* [read] is a set of variables *)
let visit var_set table =
  let useful = ref S.empty in
  (* recursively mark visited nodes which are useful *)
  let rec visit x ({ c_vars; c_useful; c_visited } as entry) = 
    if not c_visited then
      begin
        entry.c_visited <- true;
        entry.c_useful <- true;
        useful := S.add x !useful;
	S.iter visit_fathers c_vars
      end
  and visit_fathers x =
    try
      let entry = Env.find x table in
      visit x entry
    with
      Not_found -> ()
  (* look for an entry in the table that is not marked but useful *)
  and visit_table x ({ c_useful; c_visited } as entry) =
    if not c_visited && c_useful then visit x entry in
  (* recursively mark nodes and their predecessors *)
  Env.iter visit_table table;
  !useful
 
(* Add the entries [y_j <- x_1; ...; y_j <- x_n]_j in the table. *)
(* for any variable [x_j in w] and r = { x_1,...,x_n } *)
(* if [y_j] is already in the table, extends the set of variables on *)
(* which it depends. Otherwise, create a new entry *)
(* when [is_useful = true], mark all read and write variables to be useful *)
let add_dep is_useful w_set r_set table =
  let add x table =
    try
      let { c_vars; c_useful } as cont = Env.find x table in
      cont.c_vars <- S.union r_set c_vars;
      cont.c_useful <- c_useful || is_useful;
      table
    with 
    | Not_found ->
       Env.add x
	 { c_vars = r_set; c_useful = is_useful; c_visited = false } 
         table in
  (* add dependences *)
  S.fold add w_set table

(* add an entry for variables [v_set = { y_1,..., y_n }] *)
let mark is_useful v_set table =
  let add x table =
    try
      let { c_useful } as cont = Env.find x table in
      if not c_useful then cont.c_useful <- is_useful;
      table
    with
      Not_found ->
      Env.add x { c_vars = S.empty; c_useful = is_useful; c_visited = false }
        table in
  S.fold add v_set table

(* The algorithm is done in two passes. *)
(* Pass 1. compute the set of useful variables. *)
(* Pass 2. remove useless computations *)

(* First pass. Compute the def-use chains and read variables *)
let equation funs ({ def_use } as acc) ({ eq_desc; eq_write } as eq) =
  let acc_in = { acc with read = S.empty } in
  let eq, def_use = match eq_desc with
  | EQeq(p, e) ->
     let _, { def_use; read } = Mapfold.expression_it funs acc_in e in
     let { v = w } = Vars.pattern { lv = S.empty; v = S.empty } p in
     (* for every [x in w] and [y in read] add the link [x depends on y] *)
     let l_w = S.to_list w in
     let is_useful = Unsafe.expression e in
     let l_ = Env.to_list def_use in
     eq, add_dep is_useful w read def_use
  | EQder { id; e; e_opt = None; handlers = [] } | EQinit(id, e) ->
     let _, { def_use; read } = 
       Mapfold.expression_it funs acc_in e in
     let is_useful = Unsafe.expression e in
     let l_ = Env.to_list def_use in
     eq, add_dep is_useful (S.singleton id) read def_use
  | EQmatch { e; handlers } ->
     let _, { def_use; read } = 
       Mapfold.expression_it funs acc_in e in
     let _, { def_use } =
       Util.mapfold
         (Mapfold.match_handler_eq_it funs) { def_use; read = S.empty } handlers in
     (* add control dependences *)
     (* if [y in read /\ x in write(eq)] add [x depends on y] *)
     let w = Defnames.names S.empty eq_write in
     let is_useful = Unsafe.expression e in
     let l_ = Env.to_list def_use in
     eq, add_dep is_useful w read def_use
  | EQif { e; eq_true; eq_false } ->
     let _, { def_use; read } = 
       Mapfold.expression_it funs acc_in e in
     let _, acc = Mapfold.equation_it funs { def_use; read = S.empty } eq_true in
     let _, { def_use } = Mapfold.equation_it funs acc eq_false in
     (* add control dependences *)
     (* if [y in r_e /\ x in write(eq)] add [x depends on y] *)
     let w = Defnames.names S.empty eq_write in
     let is_useful = Unsafe.expression e in
     let l_ = Env.to_list def_use in
     eq, add_dep is_useful w read def_use
  | EQreset(res_eq, e) ->
     let _, { def_use; read } =
       Mapfold.expression_it funs acc_in e in
     let _, { def_use } =
       Mapfold.equation_it funs { def_use; read = S.empty } res_eq in
     (* add control dependencs *)
     (* if [y in r_e /\ x in write(res_eq)] add [x depends on y] *)
     let w = Defnames.names S.empty eq_write in
     let is_useful = Unsafe.expression e in
     let l_ = Env.to_list def_use in
     eq, add_dep is_useful w read def_use
  | _ ->
     let eq, { def_use } = Mapfold.equation funs acc_in eq in
     let l_ = Env.to_list def_use in eq, def_use in
  eq, { def_use; read = S.empty }

and expression funs ({ read } as acc) ({ e_desc } as e) =
  match e_desc with
  | Evar(id) | Elast { id } -> e, { acc with read = S.add id read }
  | Elet(leq, e_let) ->
     let _, { def_use } = Mapfold.leq_it funs { acc with read = S.empty } leq in
     let _, acc = Mapfold.expression_it funs { def_use; read } e_let in
     e, acc
  | Elocal(b, e_b) ->
     let _, { def_use } = Mapfold.block_it funs { acc with read = S.empty } b in
     let _, acc = Mapfold.expression_it funs { def_use; read } e_b in
     e, acc
  | _ -> raise Mapfold.Fallback

(* free variables that appear in the output [e] of *)
(* a function [fun x1... -> e where eq] are useful *)
let funexp funs ({ read } as acc) ({ f_body = { r_desc } } as f) =
  let v, def_use = match r_desc with
    | Exp(e) ->
       let _, { def_use; read } = Mapfold.expression_it funs acc e in
       (* variables in [e] are useful *)
       let v_ = Env.to_list def_use in
       read, def_use
    | Returns({ b_env } as b) -> 
       let _, { def_use } =
         Mapfold.block_it funs { acc with read = S.empty } b in
       (* returned variables are useful *)
       let w = Env.fold (fun x _ acc -> S.add x acc) b_env S.empty in
       let v_ = Env.to_list def_use in
       w, def_use in
  let v_ = S.to_list v in
  let def_use = mark true v def_use in
  f, { def_use; read = S.empty }
  
(* Pass 2. Remove useless computations *)
let clean_letdecl useful l_decl =
  let equation funs acc eq =
    let eq_empty = Aux.eqmake Defnames.empty EQempty in
    let { eq_desc; eq_write } as eq, _ = Mapfold.equation funs acc eq in
    match eq_desc with
    | EQeq(p, e) ->
       Aux.eq_make p e, acc
    | EQder { id; e; e_opt = None; handlers = [] } ->
       let eq = if S.mem id acc then Aux.eq_der id e else eq_empty in
       eq, acc
    | EQinit(id, e) ->
       let eq = if S.mem id acc then Aux.eq_init id e else eq_empty in
       eq, acc
    | EQmatch { e; handlers } ->
       (* remove the equation if all handlers are empty *)
       let eq = if List.for_all (fun { m_body} -> Aux.is_empty m_body) handlers
                then eq_empty
                else eq in
       eq, acc
    | EQreset(res_eq, e) ->
       (* remove the equation if the body is empty *)
       let eq = if Aux.is_empty res_eq then eq_empty else eq in
       eq, acc
    | _ -> eq, acc in
  
  (* remove useless names in write names *)
  let write_t funs acc { dv; di; der } =
    let filter set = S.filter (fun x -> S.mem x acc) set in
    { dv = filter dv; di = filter di; der = filter der }, acc in
  
  let build funs acc env =
    let env = Env.filter (fun x _ -> S.mem x acc) env in
    env, acc in
  
  (* remove useless names in a pattern. *)
  let pattern funs acc ({ pat_desc } as p) =
    match pat_desc with
    | Evarpat(x) ->
       if S.mem x acc then p, acc
       else { p with pat_desc = Ewildpat }, acc
    | Ealiaspat(p_alias, x) ->
       let p_alias, acc = Mapfold.pattern_it funs acc p_alias in
       if S.mem x acc then { p with pat_desc = Ealiaspat(p_alias, x) }, acc
       else p_alias, acc
    | _ -> raise Mapfold.Fallback in
  
  let block funs acc b =
    let ({ b_vars } as b), acc = Mapfold.block funs acc b in
    let b_vars =
    List.filter (fun { var_name = x } -> S.mem x acc) b_vars in
    { b with b_vars }, acc in
  
  let global_funs =
    { Mapfold.default_global_funs with build } in
  let funs =
    { Mapfold.defaults with global_funs; equation; write_t; pattern; block } in
  
  let l_ = S.to_list useful in
  let l_decl, _ = Mapfold.letdecl_it funs useful l_decl in
  l_decl

(* Useful function. For debugging purpose. *)
let print ff table =
  let module Printer = Printer.Make(Ptypinfo) in
  let names ff l =
    Pp_tools.print_list_r Printer.name "{" "," "}" ff (S.elements l) in
  let entry ff (x, { c_vars; c_useful }) =
    Format.fprintf ff "@[<hov 2>%a <--@ {c_vars = %a;@ c_useful = %s}@]@ "
		   Printer.name x
		   names c_vars (if c_useful then "true" else "false") in
  Format.fprintf ff
    "@[<hov 2>Def-use chains:@ %a@.@]"
    (Pp_tools.print_list_r entry "" "" "") (Env.to_list table) 

(* Main. Combine the two passes *)
let letdecl funs acc l_decl =
  (* pass 1. build the def-use chains *)
  let l_decl, { def_use } = Mapfold.letdecl funs acc l_decl in
  (* pass 2. compute useful variables; remove dead-code *)
  if !Misc.verbose then 
    Format.fprintf Format.std_formatter "%a" print def_use;
  let useful = visit S.empty def_use in
  if !Misc.verbose then 
    Format.fprintf Format.std_formatter "%a" print def_use;
  let l_decl = clean_letdecl useful l_decl in
  l_decl, acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; expression; funexp; letdecl; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

