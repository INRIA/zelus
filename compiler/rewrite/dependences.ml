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
(* dependences between equations *)
open Ident
open Zelus
open Graph

module type READ =
  sig
    val read: eq -> S.t * S.t (* reads last and current variables *)
    val def: eq -> S.t  (* defined variables *)
    val init: eq -> bool (* [init x = e] must be scheduled before reads/writes *)
    val nodep: eq -> bool (* [x = e] does not introduce any dependence for [x] *)
  end

module Make (Read:READ) =
struct
  let build eq_list =
    (* associate a graph node for each name declaration *)
    let rec nametograph g var_set n_to_graph_list =
      let add n n_to_graph_list =
	try
	  let graph_list = Env.find n n_to_graph_list in
	  Env.add n (g :: graph_list) (Env.remove n n_to_graph_list)
	with
	  Not_found -> Env.add n [g] n_to_graph_list in
      S.fold add var_set n_to_graph_list in
    
    (* finds all the nodes associated to [n] *)
    (* this is only necessary if [n] is written more than once *)
    (* during a reaction. Otherwise, a single node is associated to [n] *)
    let all n n_to_graph_list =
      try
	Env.find n n_to_graph_list
      with
	Not_found -> [] in
    
    (* first build the association table n_to_graph_list: *)
    (* [n -> [node1,...,nodek]] for every defined variable *)
    (* [eq_list] is the input list of equations *)
    let init_graph (g_list, n_to_graph_list) eq =
      let g = make eq in
      let var_set = Read.def eq in
      let n_to_graph_list = nametograph g var_set n_to_graph_list in
      g :: g_list, n_to_graph_list in
    
    let make_graph g_list n_to_graph_list =
      (* A node [g] that reads [n1,...,nk] must be scheduled after *)
      (* all the nodes that compute the [ni] *)
      (* when [is_last], reverse the dependence, i.e., [g] must be *)
      (* scheduled before *)
      let attach is_last n_to_graph_list g_node n =
        let attach g_node g =
          try
	    if Read.nodep g.g_containt then ()
	    else
	      if (g == g_node) (* && is_last *) then ()
	      else (* an equation [init x = e] must be done before *)
		   (* [last x] and [x] are read *)
		(* if Read.init g_node
		then S.union (Read.def g_node) last_names else last_names in *)
		if Read.init g.g_containt then add_depends g_node g
		else if is_last
		then add_depends g g_node else add_depends g_node g
	  with | Not_found -> () in
	let g_list = all n n_to_graph_list in
        List.iter (attach g_node) g_list in
      
      let add_node g =
	let g_node = containt g in
	let last_names, names = Read.read g_node in
        (* an equation [init x = e] must be done before *)
	(* any equation [x = ...] *)
	let last_names =
	  if Read.init g_node
	  then S.union (Read.def g_node) last_names else last_names in
	(* reads of [x] after assignment to [x] *)
	S.iter (attach false n_to_graph_list g) names;
        (* reads of [last x] done before assignment to [x] *)
	S.iter (attach true n_to_graph_list g) last_names in
      
      List.iter add_node g_list in
    
    (* build the association table *)
    let g_list, n_to_graph_list =
      List.fold_left init_graph ([], Env.empty) eq_list in
    (* then the dependence graph *)
    make_graph g_list n_to_graph_list;
    g_list
end


