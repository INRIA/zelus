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
    val init: eq -> bool (* [init x = e] must be scheduled before reads/writes *)
    val read: eq -> S.t * S.t (* reads last and current variables *)
    val def: eq -> S.t  (* defined variables *)
    val antidep: eq -> bool (* [x = e] must be scheduled after reads of [x] *)
  end

module Make (Read:READ) =
struct
  let build eq_list =
    (* associate a graph node for each name declaration *)
    let rec nametograph node var_set n_to_graph =
      S.fold (fun x acc -> Env.add x node acc) var_set n_to_graph in
    
    (* finds all the nodes associated to [n] *)
    let all n n_to_graph =
      let rec allrec acc n_to_graph =
	try
	  let g = Env.find n n_to_graph in
	  allrec (g :: acc) (Env.remove n n_to_graph)
	with
	    Not_found -> acc, n_to_graph in
      let acc, _ = allrec [] n_to_graph in
      acc in
    
    (* first build the two association tables *)
    (* init_n_to_graph: [n -> node] and n_to_graph: [n -> node] *)
    (* for every defined variable *)
    (* [eq_list] is the input list of equations *)
    let rec init_graph (node_list, init_n_to_graph, n_to_graph) eq_list =
      match eq_list with
        | [] -> (node_list, init_n_to_graph, n_to_graph)
        | eq :: eq_list ->
          let node = make eq in
          let var_set = Read.def eq in
          let init_n_to_graph, n_to_graph =
	    if Read.init eq
	    then let init_n_to_graph = 
		   nametograph node var_set init_n_to_graph in
		 init_n_to_graph, n_to_graph
	    else let n_to_graph = 
		   nametograph node var_set n_to_graph in
		 init_n_to_graph, n_to_graph in
	  init_graph 
	    (node :: node_list, init_n_to_graph, n_to_graph) eq_list in
    
    let rec make_graph node_list init_n_to_graph n_to_graph =
      (* [node] must be scheduled after all nodes associated to [n] *)
      let attach anti n_to_graph node n =
        let g_list = all n n_to_graph in
        List.iter 
	  (fun g ->  if anti then add_depends g node else add_depends node g) 
	  g_list in
      
      let rec makerec = function
        | [] -> ()
        | node :: node_list ->
          let last_names, names = Read.read (containt node) in
          (* reads of [x] after assignment to [x] *)
	  S.iter (attach false n_to_graph node) names;
          (* reads of [x] after initialization to [x] *)
	  S.iter (attach false init_n_to_graph node) names;
          (* reads of [last x] done after initialization *)
	  S.iter (attach false init_n_to_graph node) last_names;
          (* reads of [last x] done before assignment to [x] *)
	  S.iter (attach true n_to_graph node) last_names;
          makerec node_list in
      makerec node_list in
    
    let node_list, init_to_graph, n_to_graph = 
      init_graph ([], Env.empty, Env.empty) eq_list in
    
    (* every eq. [init x = e'] must be scheduled before eq. [x = e'] *)
    let before n node =
      let g_list = all n init_to_graph in
      List.iter (fun g -> add_depends node g) g_list in
    Env.iter before n_to_graph;
    (* build the dependence graph *)
    make_graph node_list init_to_graph n_to_graph;
    node_list
end


