(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2018                                               *)
(*                                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* graph manipulations *)

(* a node is a unique integer; precedence/successor is defined with it *)
(* a association table associates a containt to an index *)
type index = int

module S = Set.Make(struct type t = int let compare = compare end)
module E = Map.Make(struct type t = int let compare = compare end)

type 'a graph =
  { outputs: S.t ; (* the exits of a data-flow graph *)
    succ: S.t E.t; (* the successor of a node *)
    prec: S.t E.t; (* the predecessor of a node *)
    containt: 'a E.t; (* the value associated to a node *)
    nodes: S.t; (* the set of nodes *) }
    
type error = Cycle of index list

exception Error of error

let empty = { outputs = S.empty; succ = E.empty; prec = E.empty;
              containt = E.empty; nodes = S.empty }

(* add a node to a graph *)
let add ({ nodes; containt } as g) n v =
  { g with nodes = S.add n nodes; containt = E.add n v containt }

(* given [n1 in set1] and [n2 in set2], add (n1, n2) to succ; (n2, n1) to prec *)
let add_before ({ succ; prec } as g) set1 set2 =
  let update set x rel =
    E.update x
      (function | None -> Some(set) | Some(set0) -> Some(S.union set0 set))
      rel in
  { g with succ = S.fold (update set2) set1 succ;
           prec = S.fold (update set1) set2 prec }

(* [n1] is before [n2] *)
let before { succ } n1 n2 = S.mem n2 (E.find n1 succ)

(* containt *)
let containt { containt } n_list = List.map (fun n -> E.find n containt) n_list

(* computes outputs = nodes that have no successors *)
let outputs ({ nodes; succ } as g) =
  let outputs =
    S.filter
      (fun n -> try S.is_empty (E.find n succ) with Not_found -> true) nodes in
  { g with outputs = outputs }
        
(** Well formation of a graph *)
(* the graph must be a partial order, i.e., no cycle *)
let check { outputs; succ; prec } =
  (* check that a graph has no cycle; in case of error, return a path. *)
  (* [grey] is the set of currently visited nodes; if the current *)
  (* node is grey, then a path has been found *)
  (* [black] is the set of nodes visited in the past *)
  let rec cycle n (black, grey) =
    if S.mem n grey then raise (Error(Cycle(S.elements grey)))
    else if S.mem n black then black, grey
    else
      let black, grey =
        S.fold cycle (E.find n prec) (black, S.add n grey) in
      S.add n black, S.remove n grey in
  ignore (S.fold cycle outputs (S.empty, S.empty))

(** Topological sort. Must be applied to a well-formed graph *)
let topological { outputs; prec; containt } =
  let rec sortrec n (visited, seq) =
    if S.mem n visited then visited, seq
    else
      let n_set = E.find n prec in
      let visited, seq = S.fold sortrec n_set (visited, seq) in
      S.add n visited, (E.find n containt) :: seq in      
  let _, seq = S.fold sortrec outputs (S.empty, []) in
  List.rev seq

(** Print *)
let print p ff { nodes; prec; outputs; containt } =
  let o_list = S.elements outputs in
  let l =
    S.fold
      (fun n acc -> (n, E.find n containt, S.elements (E.find n prec)) :: acc)
      nodes [] in
  let one ff (n, v, n_list) =
    Format.fprintf ff "%d: %a depends on %a"
      n p v (Pp_tools.print_list_r Format.pp_print_int "" "," "") n_list in
  Format.fprintf ff
    "@[<0>@[<v2>dependences:@,%a@]@,@[<v2>outputs:@,%a@.@]"
    (Pp_tools.print_list_l one "" "" "") l
    (Pp_tools.print_list_r Format.pp_print_int "" "," "") o_list
