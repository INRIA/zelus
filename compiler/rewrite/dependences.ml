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
    val control: eq -> bool (* control structure *)
    val nodep: eq -> bool (* [x = e] does not introduce any dependence for [x] *)
  end

module Make (Read:READ) =
struct
  type node = { n_eq: eq; n_def: S.t; n_read: S.t * S.t }

  let build eq_list =
    (* associate a graph node for each name declaration *)
    let rec nametograph g var_set n_to_graph =
      S.fold (fun x acc -> Env.add x g acc) var_set n_to_graph in
    
    (* finds all the nodes associated to [n] *)
    (* this is only necessary if [n] is written more than once *)
    (* during a reaction. Otherwise, a single node is associated to [n] *)
    let all n n_to_graph =
      let rec allrec acc n_to_graph =
	try
	  let g = Env.find n n_to_graph in
	  allrec (g :: acc) (Env.remove n n_to_graph)
	with
	    Not_found -> acc, n_to_graph in
      let acc, _ = allrec [] n_to_graph in
      acc in
    
    (* first build the association table n_to_graph: [n -> node] *)
    (* for every defined variable *)
    (* [eq_list] is the input list of equations *)
    let init_graph (g_list, n_to_graph) eq =
      let g = make eq in
      let var_set = Read.def eq in
      let n_to_graph = nametograph g var_set n_to_graph in
      g :: g_list, nametograph g var_set n_to_graph in
    
    let make_graph g_list n_to_graph =
      (* [g] must be scheduled after all nodes associated to [n] *)
      (* when [is_last], reverse dependences *)
      let attach is_last n_to_graph g_node n =
        let attach g_node g =
          try
	    if Read.nodep g.g_containt then ()
	    else
	      (* an equation [[init] x = f(last x)] has no cycle *)
	      (* as well a for a control structure *)
	      if (g == g_node) && (is_last || Read.control g.g_containt) then ()
	      else if is_last && not (Read.init g.g_containt)
	      then add_depends g g_node else add_depends g_node g
	  with | Not_found -> () in
	let g_list = all n n_to_graph in
        List.iter (attach g_node) g_list in
      
      let add_node g =
        let g_node = containt g in
	let last_names, names = Read.read g_node in
        let last_names =
	  (* an equation [init x = e] depends on [last x] *)
	  if Read.init g_node
	  then S.union (Read.def g_node) last_names else last_names in
	(* reads of [x] after assignment to [x] *)
	S.iter (attach false n_to_graph g) names;
        (* reads of [last x] done before assignment to [x] *)
	S.iter (attach true n_to_graph g) last_names in
      
      List.iter add_node g_list in
    
    (* build the association table *)
    let g_list, n_to_graph = List.fold_left init_graph ([], Env.empty) eq_list in
    (* then the dependence graph *)
    make_graph g_list n_to_graph;
    g_list
end


