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

(* acyclic graph manipulations *)

(* a node is a unique integer; precedence/successor is defined with it *)
(* a association table associates a containt to an index *)
(* a graph is well formed if the graph is acyclic; *)
(* nodes in [outputs] have no successors; *)
(* [succ] and [prec] are inverse of each other; [nodes] is the set of nodes *)
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
let add n v ({ nodes; containt } as g) =
  { g with nodes = S.add n nodes; containt = E.add n v containt }

(* given [n1 in set1] and [n2 in set2], add (n1, n2) to succ; *)
(* (n2, n1) to prec *)
let add_before set1 set2 ({ succ; prec } as g) =
  let update set x rel =
    E.update x
      (function | None -> Some(set) | Some(set0) -> Some(S.union set0 set))
      rel in
  { g with succ = S.fold (update set2) set1 succ;
           prec = S.fold (update set1) set2 prec }

(* [n1] is before [n2] *)
let is_before { succ } n1 n2 = S.mem n2 (E.find n1 succ)

(* successors *)
let successors n { succ } = try E.find n succ with Not_found -> S.empty
                                                                  
(* containt *)
let containt n { containt } = E.find n containt

(* computes outputs = nodes that have no successors *)
(* warning: the graph must be acyclic. In case it is cyclic *)
(* nodes on a cycle are not considered to be outputs *)
let outputs ({ nodes; succ } as g) =
  let outputs =
    S.filter
      (fun n -> try S.is_empty (E.find n succ) with Not_found -> true) nodes in
  { g with outputs = outputs }
        
(** Well formation of a graph *)
(* the graph must be a partial order, i.e., acyclic *)
let acyclic { succ; prec } =
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
  ignore (E.fold (fun n _ acc -> cycle n acc) prec (S.empty, S.empty))

(** Topological sort. Must be applied to a well-formed graph *)
let topological { outputs; prec } =
  let rec sortrec n (visited, seq) =
    if S.mem n visited then visited, seq
    else
      let n_set = try E.find n prec with Not_found -> S.empty in
      let visited, seq = S.fold sortrec n_set (visited, seq) in
      S.add n visited, n :: seq in      
  let _, seq = S.fold sortrec outputs (S.empty, []) in
  List.rev seq

(** transitive reduction for an acyclic graph *)
(* returns the same acyclic graph where *)
(* [prec] and [succ] are reduced *)
let transitive_reduction ({ outputs; nodes; prec; succ } as g) =
  (* three steps: the first step computes a topological sort *)
  let l = topological g in
  (* the second computes the longest path value [v] for every node *)
  let length length_table n =
    let v =
      S.fold
        (fun m acc -> max acc (E.find m length_table))
        (try E.find n prec with Not_found -> S.empty) 0 in
    E.add n (v+1) length_table in
  let length_table = List.fold_left length E.empty l in
  (* the third step keeps the link from [source] to [target] *)
  (* if length_table[target] = length_table[source] + 1 *)
  let reduce (new_prec, new_succ) n =
    let v = E.find n length_table in
    let l_prec = try E.find n prec with Not_found -> S.empty in
    let l_prec = S.filter (fun m -> (E.find m length_table) = v - 1) l_prec in
    let l_succ = try E.find n succ with Not_found -> S.empty in
    let l_succ = S.filter (fun m -> (E.find m length_table) = v + 1) l_succ in
    let new_prec =
      if S.is_empty l_prec then new_prec else E.add n l_prec new_prec in
    let new_succ =
      if S.is_empty l_succ then new_succ else E.add n l_succ new_succ in
    new_prec, new_succ in
  let new_prec, new_succ = List.fold_left reduce (E.empty, E.empty) l in
  { g with prec = new_prec; succ = new_succ }
     
let topological ({ containt } as g) =
  let seq = topological g in
  List.map (fun n -> E.find n containt) seq

(** Print *)
let print p ff { nodes; succ; outputs; containt } =
  let o_list = S.elements outputs in
  let l =
    S.fold
      (fun n acc ->
         try
           (n, E.find n containt, S.elements (E.find n succ)) :: acc
         with
         Not_found -> acc)
      nodes [] in
  let one ff (n, v, n_list) =
    Format.fprintf ff "%d: %a before %a"
      n p v (Pp_tools.print_list_r Format.pp_print_int "" "," "") n_list in
  Format.fprintf ff
    "@[<0>@[<v2>dependences:@,%a@]@,@[<v2>outputs:@,%a@.@]"
    (Pp_tools.print_list_l one "" "" "") l
    (Pp_tools.print_list_r Format.pp_print_int "" "," "") o_list
