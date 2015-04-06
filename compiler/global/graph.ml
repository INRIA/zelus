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
(* graph manipulation *)

(* a graph is a set of nodes and edges. [g_top] is the list of nodes with  *)
(* no predecessors whereas [g_bot] is the list of nodes with no successors *)

type 'a graph =
  { g_top: 'a node list;
    g_bot: 'a node list }

and 'a node =
  { g_containt: 'a;
    g_tag: int;
    mutable g_visited: bool;
    mutable g_mark: int;
    mutable g_depends_on: 'a node list;
    mutable g_depends_by: 'a node list;
  }

exception Cycle of int (* returns the index of the node *)

let tag = ref 0
let new_tag () = incr tag; !tag
let containt g = g.g_containt
let linked g1 g2 =
  (List.memq g2 g1.g_depends_on) || (List.memq g1 g2.g_depends_on)
let make c =
  { g_containt = c; g_tag = new_tag (); g_visited = false;
    g_mark = - 1; g_depends_on = []; g_depends_by = [] }

let union n_list1 n_list2 =
  List.fold_left 
    (fun acc node -> if List.memq node n_list1 then acc else node :: acc)
    n_list1 n_list2

let add node n_list = if List.memq node n_list then n_list else node :: n_list

(* direct dependences *)
let prec g_list = List.fold_left (fun acc g -> union acc g.g_depends_on) [] g_list


(** Add a dependence. [add_depends node1 node2] makes [node1] also depend *)
(** on [node2] *)
let add_depends node1 node2 =
  node1.g_depends_on <- add node2 node1.g_depends_on;
  node2.g_depends_by <- add node1 node2.g_depends_by
let graph top_list bot_list = { g_top = top_list; g_bot = bot_list }

let print { g_bot = bot_list } =
  let rec print acc g =
    if g.g_visited then acc
    else
      begin
        g.g_visited <- true;
        let acc =
          (containt g, g.g_mark, List.map containt g.g_depends_on) :: acc in
        List.fold_left print acc g.g_depends_on
      end in
  let acc = List.fold_left print [] bot_list in
  let bot_list = List.map containt bot_list in
  bot_list, acc

(** Topological sort *)
let topological g_list =
  let rec sortrec g_list seq =
    match g_list with
    | [] -> seq
    | g :: g_list ->
        if g.g_visited then sortrec g_list seq
        else
          begin
            g.g_visited <- true;
            let seq = sortrec g.g_depends_on seq in
            sortrec g_list (g :: seq)
          end in
  let seq = sortrec g_list [] in
  List.iter
    (fun ({ g_visited = _ } as node) -> node.g_visited <- false) g_list;
  List.rev seq

(** Detection of cycles *)
(* Mark nodes with: *)
(*  - -1 initially, for unvisited nodes *)
(*  - 0 for "opened" nodes, currently visited, while visiting its descendents*)
(*  - 1 for "closed" nodes, visited once, no circuits found from it. *)
(*  A circuit is found when a node marked with 0 is visited again.*)
let cycle { g_bot = g_list } =
  (* store nodes in a stack *)
  let s = Stack.create () in
  (* flush the connected component *)
  let rec flush index =
    if Stack.is_empty s then []
    else let v = Stack.top s in
         if v.g_tag = index then let _ = Stack.pop s in []
         else let v = Stack.pop s in
              v.g_containt :: flush index in

  let rec visit g =
    match g.g_mark with
      | -1 ->
          (* Unvisited yet *)
          (* Open node *)
          Stack.push g s;
          g.g_mark <- 0;
          (* Visit descendents *)
          List.iter visit g.g_depends_on;
          (* Close node *)
          ignore (Stack.pop s);
          g.g_mark <- 1
      | 0 ->
          (* Visit an opened node (visited and not close) : circuit *)
          raise (Cycle g.g_tag)
      | 1 | _ ->
          (* Visit a closed node (no existing circuit) : pass *)
          () in
  try
    List.iter visit g_list; None
  with
    | Cycle(index) -> Some(flush index)

let accessible useful_nodes graph =
  let rec follow g =
    if not g.g_visited then
      begin
        g.g_visited <- true;
        List.iter follow g.g_depends_on
      end in
  let read acc g =
    if g.g_visited then begin g.g_visited <- false; g :: acc end else acc in
  List.iter follow useful_nodes;
  List.fold_left read [] graph.g_bot
