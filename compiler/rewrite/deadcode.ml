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
open Deftypes

(** Dead-code removal. First build a table [yn -> {x1,...,xk}] wich associate *)
(** the list of read variables used to produce yn *)
(** then recursively mark all useful variable according to *)
(** read-in dependences *)
(** An equation [eq] is marked useful when it may be unsafe, that *)
(** is, it has side effets and/or is non total *)
(** For the moment, only combinatorial functions *)
(** are considered safe. *)
(** finally, only keep equations and name defs. for useful variables *)
(** horizons are considered to be useful *)
type table = cont Env.t
 and cont = 
   { mutable c_vars: S.t; (* set of variables *)
     mutable c_useful: bool; (* is-it a useful variable? *)
     mutable c_visited: bool; (* has it been visited already? *) }
     
(** Useful function. For debugging purpose. *)
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
	let { c_useful = u } as cont = Env.find x table in
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
      let { c_vars = l; c_useful = u } as cont = Env.find x table in
      cont.c_vars <- S.union r l;
      cont.c_useful <- u || is_useful;
      table
    with 
    | Not_found ->
       Env.add x
	       { c_vars = r; c_useful = is_useful; c_visited = false } table in
  (* mark all vars. in [r] to be useful *)
  let table = if is_useful then mark_useful r table else table in
  (* add dependences *)
  S.fold add w table

	 
(** Extend [table] where every entry [y -> {x1,...,xn}] *)
(** is marked to also depend on names in [names] *)
let extend table names =
  Env.map 
    (fun ({ c_vars = l } as cont) -> { cont with c_vars = S.union l names })
    table

(** Fusion of two tables *)
let merge table1 table2 =
  let add x ({ c_vars = l1; c_useful = u1 } as cont1) table =
    try
      let ({ c_vars = l2; c_useful = u2 } as cont2) = Env.find x table in
      cont2.c_vars <- S.union l1 l2; cont2.c_useful <- u1 || u2;
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
     let r = fve S.empty e in
     add (Unsafe.exp e) w r table
  | EQpluseq(n, e) | EQinit(n, e)
  | EQder(n, e, None, []) -> 
     let r = fve S.empty e in
     add (Unsafe.exp e) (S.singleton n) r table
  | EQmatch(_, e, m_h_list) ->
     let r = fve S.empty e in
     let u = Unsafe.exp e in
     (* mark read variables to be useful when [e] is potentially unsafe *)
     let table = add u S.empty r table in
     let table_b =
       List.fold_left
	 (fun table { m_body = b } -> build_block table b)
	 Env.empty m_h_list in
     merge table (extend table_b r)
  | EQreset(res_eq_list, e) ->
     let r = fve S.empty e in
     let u = Unsafe.exp e in
     (* mark read variables to be useful when [e] is potentially unsafe *)
     let table = add u S.empty r table in
     let table_res = build_equation_list Env.empty res_eq_list in
     merge table (extend table_res r)
  | EQforall { for_index = i_list; for_init = init_list;
               for_body = b_eq_list } ->
     let index table { desc = desc } =
       match desc with
       | Einput(i, e) ->
	  add (Unsafe.exp e) (S.singleton i) (fve S.empty e) table
       | Eoutput(i, j) ->
	  add false (S.singleton j) (S.singleton i) table
       | Eindex(i, e1, e2) ->
	  add ((Unsafe.exp e1) || (Unsafe.exp e2))
	      (S.singleton i) (fve (fve S.empty e1) e2) table in
     let init table { desc = desc } =
       match desc with
       | Einit_last(i, e) ->
	  add (Unsafe.exp e) (S.singleton i) (fve S.empty e) table in
     let table = List.fold_left index table i_list in
     let table = List.fold_left init table init_list in
     build_block table b_eq_list
  | EQand(eq_list) | EQbefore(eq_list) -> build_equation_list table eq_list
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
  let useful = ref S.empty in
  (* recursively mark visited nodes which are useful *)
  let rec visit x ({ c_vars = l; c_useful = u; c_visited = v } as entry) = 
    if not v then
      begin
        entry.c_visited <- true;
        entry.c_useful <- true;
        useful := S.add x !useful;
	S.iter visit_fathers l
      end
  and visit_fathers x =
    useful := S.add x !useful;
    try
      let entry = Env.find x table in
      visit x entry
    with
      Not_found -> ()
  (* look for an entry in the table that is not marked but useful *)
  and visit_table x ({ c_useful = u; c_visited = v } as entry) =
    if not v && u then visit x entry in
  (* recursively mark nodes and their predecessors *)
  S.iter visit_fathers read;
  Env.iter visit_table table;
  !useful

(** Empty block *)
let is_empty_block { b_locals = l; b_body = eq_list } =
  (l = []) && (eq_list = [])

(** remove useless names in write names *)
let writes useful { dv = dv; di = di; der = der; nv = nv; mv = mv } =
  let filter set = S.filter (fun x -> S.mem x useful) set in
  { dv = filter dv; di = filter di; der = filter der;
    nv = filter nv; mv = filter mv }
			
(* remove useless names in a pattern *)
let rec pattern useful ({ p_desc = desc } as p) =
  match desc with
  | Ewildpat | Econstpat _ | Econstr0pat _ -> p
  | Etuplepat(p_list) ->
     { p with p_desc = Etuplepat(List.map (pattern useful) p_list) }
  | Econstr1pat(c, p_list) ->
     { p with p_desc = Econstr1pat(c, List.map (pattern useful) p_list) }
  | Evarpat(x) -> if S.mem x useful then p else { p with p_desc = Ewildpat }
  | Ealiaspat(p_alias, x) ->
     let p_alias = pattern useful p_alias in
     if S.mem x useful then { p with p_desc = Ealiaspat(p_alias, x) }
     else p_alias
  | Eorpat(p1, p2) ->
     { p with p_desc = Eorpat(pattern useful p1, pattern useful p2) }
  | Erecordpat(ln_pat_list) ->
     { p with p_desc =
                Erecordpat(List.map (fun (ln, p) ->
                               (ln, pattern useful p)) ln_pat_list) }
  | Etypeconstraintpat(p, ty_exp) ->
     let p = pattern useful p in
     { p with p_desc = Etypeconstraintpat(p, ty_exp) }

(** Remove useless equations. [useful] is the set of useful names *)
let rec remove_equation useful
			({ eq_desc = desc; eq_write = w } as eq) eq_list =
  match desc with
  | EQeq(p, e) ->
     let w = fv_pat S.empty S.empty p in
     if Unsafe.exp e || S.exists (fun x -> S.mem x useful) w
     then (* the equation is useful *)
       { eq with eq_desc = EQeq(pattern useful p, e) } :: eq_list else eq_list
  | EQpluseq(n, e) | EQder(n, e, None, [])
  | EQinit(n, e) ->
     if Unsafe.exp e || S.mem n useful then eq :: eq_list else eq_list
  | EQmatch(total, e, m_h_list) ->
     let m_h_list = 
       List.map
	 (fun ({ m_body = b } as m_h) ->
	  { m_h with m_body = remove_block useful b }) m_h_list in
     (* remove the equation if all handlers are empty *)
     if not (Unsafe.exp e)
	&& List.for_all (fun { m_body = b} -> is_empty_block b) m_h_list
     then eq_list
     else { eq with eq_desc = EQmatch(total, e, m_h_list);
		    eq_write = writes useful w } :: eq_list
  | EQreset(res_eq_list, e) ->
     let res_eq_list = remove_equation_list useful res_eq_list in
     (* remove the equation if the body is empty *)
     if not (Unsafe.exp e) && res_eq_list = [] then eq_list
     else { eq with eq_desc = EQreset(res_eq_list, e);
		    eq_write = writes useful w } :: eq_list
  | EQforall({ for_index = i_list; for_init = init_list; for_body = b_eq_list;
	       for_in_env = in_env; for_out_env = out_env } as f_body) ->
     let index acc ({ desc = desc } as ind) =
       match desc with
       | Einput(i, e) ->
	  if (Unsafe.exp e) || (S.mem i useful) then ind :: acc else acc
       | Eoutput(xo, o) ->
	  if (S.mem xo useful) || (S.mem o useful) then ind :: acc else acc
       | Eindex _ ->
	  (* the index i in [e1 .. e2] is kept *)
	  ind :: acc in
     let init acc ({ desc = desc } as ini) =
       match desc with
       | Einit_last(i, e) ->
	  if (Unsafe.exp e) || (S.mem i useful) then ini :: acc else acc in
     let i_list = List.fold_left index [] i_list in
     let init_list = List.fold_left init [] init_list in
     let b_eq_list = remove_block useful b_eq_list in
     let in_env = Env.filter (fun x entry -> S.mem x useful) in_env in
     let out_env = Env.filter (fun x entry -> S.mem x useful) out_env in
     if is_empty_block b_eq_list then eq_list
     else { eq with eq_desc =
                      EQforall { f_body with
                                 for_index = i_list;
				 for_init = init_list;
				 for_body = b_eq_list;
				 for_in_env = in_env;
				 for_out_env = out_env } } :: eq_list
  | EQbefore(before_eq_list) ->
     let before_eq_list = remove_equation_list useful before_eq_list in
     (* remove the equation if the body is empty *)
     if before_eq_list = [] then eq_list
     else (Zaux.before before_eq_list) :: eq_list
  | EQand(and_eq_list) ->
     let and_eq_list = remove_equation_list useful and_eq_list in
     (* remove the equation if the body is empty *)
     if and_eq_list = [] then eq_list
     else (Zaux.par and_eq_list) :: eq_list
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
  let n_list =
    List.filter (fun { vardec_name = x } -> S.mem x useful) n_list in
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
    match sort with
    | Smem { m_kind = Some(Horizon) } -> S.add h acc | _ -> acc in
  Env.fold take l_env read
    
(** the main entry for expressions. Warning: [e] must be in normal form *)
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
           
let implementation impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
  | Efundecl(n, ({ f_body = e } as body)) ->
     { impl with desc = Efundecl(n, { body with f_body = exp e }) }
       
let implementation_list impl_list = Misc.iter implementation impl_list
