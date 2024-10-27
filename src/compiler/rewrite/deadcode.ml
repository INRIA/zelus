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

(* dead-code removal. *)
(* this is applied to normalized code *)

open Misc
open Ident
open Vars
open Zelus
open Defnames
open Deftypes

(* Dead-code removal. First build a table [yn -> {x1,...,xk}] wich associate *)
(* the list of read variables used to produce yn *)
(* then recursively mark all useful variable according to *)
(* read-in dependences *)
(* An equation [eq] is marked useful when it may be unsafe, that *)
(* is, it has side effets and/or is non total *)
(* For the moment, only combinatorial functions *)
(* are considered safe. *)
(* finally, only keep equations and name defs. for useful variables *)
(* horizons are considered to be useful *)
type table = cont Env.t
 and cont = 
   { mutable c_vars: S.t; (* set of variables *)
     mutable c_useful: bool; (* is-it a useful variable? *)
     mutable c_visited: bool; (* has it been visited already? *) }
     
(* Useful function. For debugging purpose. *)
let print ff table =
  let names ff l =
    Pp_tools.print_list_r Printer.name "{" "," "}" ff (S.elements l) in
  let entry x { c_vars = l; c_useful = u } =
    Format.fprintf ff "@[%a -> {c_vars = %a; c_useful = %s}@]@ "
		   Printer.name x
		   names l (if u then "true" else "false") in
  Env.iter entry table 

(* Add the entries [x_j <- x1; ...; x_j <- xn] in the table. *)
(* for any variable [x_j in w] *)
(* if [x_j] already, extends the set of variables on which it depends. *)
(* Otherwise, add the new entry *)
(* when [is_useful = true], mark all read and write variables to be useful *)
let add is_useful w r table =
  (* mark all names in [set] to be useful *)
  let mark_useful set table =
    let mark x table =
      try
	let { c_useful } as cont = Env.find x table in
	cont.c_useful <- true;
	table
      with
      | Not_found ->
	 Env.add x
		 { c_vars = S.empty; c_useful = true;
		   c_visited = false } table in
    S.fold mark set table in
  
  let add x table =
    try
      let { c_vars; c_useful } as cont = Env.find x table in
      cont.c_vars <- S.union r c_vars;
      cont.c_useful <- c_useful || is_useful;
      table
    with 
    | Not_found ->
       Env.add x
	       { c_vars = r; c_useful = is_useful; c_visited = false } table in
  (* mark all vars. in [r] to be useful *)
  let table = if is_useful then mark_useful r table else table in
  (* add dependences *)
  S.fold add w table

	 
(* Extend [table] where every entry [y -> {x1,...,xn}] *)
(* is marked to also depend on names in [names] *)
let extend table names =
  Env.map 
    (fun ({ c_vars } as cont) -> { cont with c_vars = S.union c_vars names })
    table

(* Fusion of two tables *)
let merge table1 table2 =
  let add x ({ c_vars = l1; c_useful = u1 } as cont1) table =
    try
      let ({ c_vars = l2; c_useful = u2 } as cont2) = Env.find x table in
      cont2.c_vars <- S.union l1 l2; cont2.c_useful <- u1 || u2;
      table
    with 
    | Not_found -> Env.add x cont1 table in
  Env.fold add table2 table1

(* Build the association table [yk -> { x1,..., xn}] *)     
let equation funs table eq =
  let { eq_desc } as eq, table = Mapfold.equation_it funs table eq in
  let eq, table =
    match eq_desc with
    | EQeq(p, e) ->
       let { v = w } = Vars.pattern { lv = S.empty; v = S.empty } p in
       let { v = r } = Vars.expression { lv = S.empty; v = S.empty } e in
       (* for every [x in w], add the link [x -> {x1, ..., xn }] to table *)
       eq, add (Unsafe.expression e) w r table
    | _ -> eq, table in
  eq, table
  
(* Visit the table: recursively mark all useful variables *)
(* returns the set of useful variables *)
(* [read] is a set of variables *)
let visit read table =
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
    useful := S.add x !useful;
    try
      let entry = Env.find x table in
      visit x entry
    with
      Not_found -> ()
  (* look for an entry in the table that is not marked but useful *)
  and visit_table x ({ c_useful; c_visited } as entry) =
    if not c_visited && c_useful then visit x entry in
  (* recursively mark nodes and their predecessors *)
  S.iter visit_fathers read;
  Env.iter visit_table table;
  !useful

(* remove useless names in write names *)
let writes useful { dv; di; der } =
  let filter set = S.filter (fun x -> S.mem x useful) set in
  { dv = filter dv; di = filter di; der = filter der }
			
(* remove useless names in a pattern. [useful] is the set of useful names *)
let pattern funs useful ({ pat_desc } as p) =
  match pat_desc with
  | Evarpat(x) ->
     if S.mem x useful then p, useful else { p with pat_desc = Ewildpat }, useful
  | Ealiaspat(p_alias, x) ->
     let p_alias, acc = Mapfold.pattern funs useful p_alias in
     if S.mem x useful then { p with pat_desc = Ealiaspat(p_alias, x) }, useful
     else p_alias, useful
  | _ -> raise Mapfold.Fallback

let eq_empty = Aux.eqmake Defnames.empty EQempty

(* Remove useless equations. [useful] is the set of useful names *)
let equation funs useful eq =
  let { eq_desc; eq_write } as eq, useful = Mapfold.equation_it funs useful eq in
  match eq_desc with
  | EQeq(p, e) ->
     let { v = w } = Vars.pattern { lv = S.empty; v = S.empty } p in
     if Unsafe.expression e || S.exists (fun x -> S.mem x useful) w
     then (* the equation is useful *)
       { eq with eq_desc = EQeq(p, e) }, useful
     else eq_empty, useful
  | EQder { id; e; e_opt = None; handlers = [] } | EQinit(id, e) ->
     if Unsafe.expression e || S.mem id useful then eq, useful
     else eq_empty, useful
  | EQmatch { e; handlers } ->
     (* remove the equation if all handlers are empty *)
     if not (Unsafe.expression e)
	&& List.for_all (fun { m_body} -> Aux.is_empty m_body) handlers
     then eq_empty, useful
     else { eq with eq_desc; eq_write = writes useful eq_write }, useful
  | EQreset(res_eq, e) ->
     (* remove the equation if the body is empty *)
     if not (Unsafe.expression e) && Aux.is_empty res_eq then eq_empty, useful
     else { eq with eq_desc; eq_write = writes useful eq_write }, useful
  | _ -> eq, useful
				     
let block funs useful ({ b_vars; b_body; b_write; b_env } as b) =
  let b_body, useful = Mapfold.equation_it funs useful b_body in
  let b_vars =
    List.filter (fun { var_name = x } -> S.mem x useful) b_vars in
  let b_env = Env.filter (fun x entry -> S.mem x useful) b_env in
  let dv = S.filter (fun x -> S.mem x useful) b_write.dv in
  { b with b_vars; b_body; b_write = { b_write with dv  }; b_env }

let leq funs useful ({ l_eq; l_env } as l) =
  let eq, useful = Mapfold.equation_it funs useful l_eq in
  let l_env = Env.filter (fun x entry -> S.mem x useful) l_env in
  { l with l_eq; l_env = l_env }

(* the main entry for expressions. Warning: [e] must be in normal form *)
let exp ({ e_desc = desc } as e) =
  match desc with
  | Elet(l, e_let) ->
     let read = fve S.empty e_let in
     (* horizons are considered as outputs *)
     let read = horizon read l in
     let table = build_local Env.empty l in
     (* Format.printf "%a@.@." print table; *)
     let useful = visit read table in
     (* Format.printf "%a@." print table; flush stdout; *)
     let { l_eq = eq_list } as l = remove_local useful l in
     if eq_list = [] then e_let else { e with e_desc = Elet(l, e_let) }
  | _ -> e
           
let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with expression; equation; result; block;
                            reset_e; reset_eq; match_handler_eq;
                            match_handler_e; present_handler_eq;
                            present_handler_e; if_eq;
                            set_index; get_index; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs empty p in
  { p with p_impl_list = p_impl_list }

