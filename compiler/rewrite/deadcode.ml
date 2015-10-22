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
(* dead-code removal. *)

open Misc
open Ident
open Vars
open Zelus
open Deftypes

(** Dead-code removal. First build a table [yn -> {x1,...,xk}] wich associate *)
(** the list of read variables used to produce yn *)
(** then recursively mark all useful variable according to read-in dependences *)
(** finally, only keep equations and name defs. for useful variables *)
(** horizons are considered to be useful *)
(** the optimization is not very agressive, e.g., stateful function calls *)
(** are still not removed *)
type table = cont Env.t
and cont = 
    { mutable c_vars: S.t; (* set of variables *)
      mutable c_useful: bool; (* is-it a useful variable? *)
    }

(** Useful function. For debugging purpose. *)
let print ff table =
  let names ff l =
    Pp_tools.print_list_r Printer.name "{" "," "}" ff (S.elements l) in
  let entry x { c_vars = l; c_useful = u } =
    Format.fprintf ff "@[%a -> {c_vars = %a; c_useful = %s}@]@ "
		   Printer.name x
		   names l (if u then "true" else "false") in
  Env.iter entry table 

(** Add an entry [x, {x1,...,xn}] to a table. If x already exists *)
(** extends its definition. Otherwise, add the new entry *)
let add w r table =
  let add x table =
    try
      let ({ c_vars = l } as cont) = Env.find x table in
      cont.c_vars <- S.union r l;
      table
    with 
    | Not_found ->
       Env.add x { c_vars = r; c_useful = false } table in
  S.fold add w table
	 
(** Extend [table] where every entry [y -> {x1,...,xn}] *)
(** is marked to also depend on names in [names] *)
let extend table names =
  Env.map 
    (fun ({ c_vars = l } as cont) -> { cont with c_vars = S.union l names })
    table

(** Fusion of two tables *)
let merge table1 table2 =
  let add x ({ c_vars = l1 } as cont1) table =
    try
      let ({ c_vars = l2 } as cont2) = Env.find x table in
      cont2.c_vars <- S.union l1 l2;
      table
  with 
    | Not_found -> Env.add x cont1 table in
  Env.fold add table2 table1

(** Build the association table [yk -> { x1,..., xn}] *)     
let rec build_equation table { eq_desc = desc } =
  match desc with
    | EQeq(p, e) ->
       let w = fv_pat S.empty S.empty p in
       (* for every [x in w], add the link [x -> {x1, ..., xn }] to table *)
       let r = fv S.empty e in
       add w r table
    | EQpluseq(n, e) | EQinit(n, e) | EQder(n, e, None, []) -> 
       let r = fv S.empty e in
       add (S.singleton n) r table
    | EQmatch(_, e, m_h_list) ->
        let r = fv S.empty e in
        let table_b =
	  List.fold_left
	    (fun table { m_body = b } -> build_block table b)
	    Env.empty m_h_list in
	merge table (extend table_b r)
    | EQreset(res_eq_list, e) ->
        let r = fv S.empty e in
	let table_res = build_equation_list Env.empty res_eq_list in
	merge table (extend table_res r)
    | EQblock _ | EQder _ | EQnext _ | EQautomaton _
    | EQpresent _ | EQemit _ -> assert false

and build_block table { b_body = eq_list } = build_equation_list table eq_list
  
and build_local table { l_eq = eq_list } = build_equation_list table eq_list
  
and build_equation_list table eq_list =
  List.fold_left build_equation table eq_list

(** Visit the table: recursively mark all useful variables *)
(** returns the set of useful variables *)
(** [read] is a set of variables *)
let visit read table =
  let useful = ref read in
  (* recursively mark visited nodes which are necessary *)
  let rec visit x ({ c_vars = l; c_useful = u } as entry) = 
    if not u then
        begin
          entry.c_useful <- true;
          useful := S.add x !useful;
	  S.iter visit_table l
        end
  and visit_table x =
    try
      let entry = Env.find x table in
      visit x entry
    with
      Not_found -> useful := S.add x !useful in
  (* recursively mark nodes and their predecessors *)
  S.iter visit_table read;
  !useful

(** Empty block *)
let is_empty_block { b_locals = l; b_body = eq_list } =
  (l = []) && (eq_list = [])

(** remove useless names in write names *)
let writes useful { dv = dv; di = di; der = der } =
  let filter set = S.filter (fun x -> S.mem x useful) set in
  { dv = filter dv; di = filter di; der = filter der }
			
(** Remove useless equations. [useful] is the set of useful names *)
let rec remove_equation useful ({ eq_desc = desc; eq_write = w } as eq) eq_list =
  match desc with
    | EQeq(p, e) ->
       let w = fv_pat S.empty S.empty p in
       if S.exists (fun x -> S.mem x useful) w
       then (* the equation is useful *) eq :: eq_list else eq_list
    | EQpluseq(n, e) | EQder(n, e, None, []) | EQinit(n, e) ->
       if S.mem n useful then eq :: eq_list else eq_list
    | EQmatch(total, e, m_h_list) ->
       let m_h_list = 
         List.map
	   (fun ({ m_body = b } as m_h) ->
	     { m_h with m_body = remove_block useful b }) m_h_list in
       (* remove the equation if all handlers are empty *)
       if List.for_all (fun { m_body = b} -> is_empty_block b) m_h_list
       then eq_list
       else { eq with eq_desc = EQmatch(total, e, m_h_list);
		      eq_write = writes useful w } :: eq_list
    | EQreset(res_eq_list, e) ->
       let res_eq_list = remove_equation_list useful res_eq_list in
       (* remove the equation if the body is empty *)
       if res_eq_list = [] then eq_list
       else { eq with eq_desc = EQreset(res_eq_list, e);
		      eq_write = writes useful w } :: eq_list
    | EQnext _ | EQder _ | EQautomaton _ | EQblock _ 
    | EQpresent _ | EQemit _ -> assert false
				       
and remove_equation_list useful eq_list =
  List.fold_right (remove_equation useful) eq_list []
		  
and remove_block useful 
		 ({ b_vars = n_list; b_locals = l_list;
		    b_body = eq_list; 
		    b_write = ({ dv = w } as defnames);
		    b_env = n_env } as b) =
  let l_list = List.map (remove_local useful) l_list in
  let eq_list = remove_equation_list useful eq_list in
  let n_list = List.filter (fun x -> S.mem x useful) n_list in
  let n_env = Env.filter (fun x entry -> S.mem x useful) n_env in
  let w = S.filter (fun x -> S.mem x useful) w in
  { b with b_vars = n_list; b_locals = l_list; b_body = eq_list; 
    b_write = { defnames with dv = w }; b_env = n_env }

and remove_local useful ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list = remove_equation_list useful eq_list in
  let l_env = Env.filter (fun x entry -> S.mem x useful) l_env in
  { l with l_eq = eq_list; l_env = l_env }

(** Compute the set of horizons *)
let horizon read { l_env = l_env } =
  let take h { t_sort = sort } acc =
    match sort with | Smem { m_kind = Some(Horizon) } -> S.add h acc | _ -> acc in
  Env.fold take l_env read
    
(** the main entry for expressions. Warning: [e] must be in normal form *)
let exp ({ e_desc = desc } as e) =
  match desc with
    | Elet(l, e_let) ->
        let read = fv S.empty e_let in
	(* horizons are considered as outputs *)
	let read = horizon read l in
	let table = build_local Env.empty l in
	(* Format.printf "%a@.@." print table; *)
	let useful = visit read table in
	(* Format.printf "%a@." print table; flush stdout; *)
	let { l_eq = eq_list } as l = remove_local useful l in
	if eq_list = [] then e_let else { e with e_desc = Elet(l, e_let) }
    | _ -> e
        
let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
