(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
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
    val read: eq -> S.t
    val def: eq -> S.t
    val antidep: eq -> bool
  end

module Make (Read:READ) =
  struct
    let build eq_list =
      (* associate a graph node for each name declaration *)
      let rec nametograph node var_set n_to_graph =
        S.fold (fun x acc -> Env.add x node acc) var_set n_to_graph in
        
      (* first build the association [n -> node] *)
      (* for every defined variable *)
      (* [eq_list] is the input list of equations *)
      (* [n_to_graph] the association *)
      let rec init_graph (node_list, n_to_graph) eq_list =
        match eq_list with
          | [] -> (node_list, n_to_graph)
          | eq :: eq_list ->
              let node = make eq in
              let var_set = Read.def eq in
              let n_to_graph = nametograph node var_set n_to_graph in
              init_graph (node :: node_list, n_to_graph) eq_list in
        
      let rec make_graph node_list n_to_graph =
        let attach node n =
          try
            let g = Env.find n n_to_graph in
              if Read.antidep g.g_containt
              then add_depends g node
              else add_depends node g
          with
            | Not_found -> () in
          
        let rec makerec = function
          | [] -> ()
          | node :: node_list ->
              let names = Read.read (containt node) in
              S.iter (attach node) names;
              makerec node_list in
        makerec node_list in

      let node_list, n_to_graph = init_graph ([], Env.empty) eq_list in
      make_graph node_list n_to_graph;
      node_list
  end
