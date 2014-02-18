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
(* causality check of scheduling constraints *)

open Misc
open Location
open Ident
open Graph
open Format

(* x = x + 1 is rejected because read(x) < write(x) is not causal *)
(* build a dependency graph and checks for cycles *)

(* constraints are of the form: *)
(* c ::= |  c < c     in sequence in a step *)
(*       |  c # c     one or the other during a step *)
(*       |  c || c    both in a step *)
(*       |  write(x)  *)
(*       |  last(x)   *)
(*       |  next(x)   *)
(* with k = { D, C } *)
(* a constraint [c] is causal iff it never contains constraints of the *)
(* form: read(x) < write(x), write(x) || write(x), write(x) < write(x) *)
(* Currently, we only have to check for cycles in the dependence graph *)

(* scheduling constraints *)
type constraints =
  | Cor of constraints * constraints
  | Cand of constraints * constraints
  | Cseq of constraints * constraints
  | Cwrite of Ident.t
  | Cread of Ident.t
  | Clastread of Ident.t
  | Cempty

type kind = Read | Write

let print_constraint ff c =
  let rec print priority ff c =
    begin match c with
      | Cseq(c1, c2) ->
          (if priority > 1
          then fprintf ff "[@(%a@ < %a)@]"
            else fprintf ff "@[%a@] <@ @[%a@]")
            (print 1) c1 (print 1) c2
      | Cand(c1, c2) ->
          (if priority > 0
          then fprintf ff "@[(%a || %a)@]"
          else fprintf ff "@[%a@] ||@ @[%a@]")
            (print 0) c1 (print 0) c2
      | Cor(c1, c2) ->
          (if priority > 0
           then fprintf ff "@[(%a # %a)@]"
           else fprintf ff "%a #@ %a")
            (print 0) c1 (print 0) c2
      | Cwrite(m) -> fprintf ff "%s" (Ident.source m)
      | Cread(m) -> fprintf ff "^%s" (Ident.source m)
      | Clastread(m) -> fprintf ff "last %s" (Ident.source m)
      | Cempty -> fprintf ff "{}"
    end in
    fprintf ff "@[%a@]@?" (print 0) c


(** Print a cycle. The cycle [n1;...;nk] is printed [n1 --> n2;...;nk --> n1] *)
(** but we remove doublons [n1 --> n1] that may appear *)
let print_cycle ff l =
  let rec print first ff l =
    match l with
      | [] -> ()
      | [n] -> 
          (* if first <> n
          then *) fprintf ff "%s --> %s" (Ident.source n) (Ident.source first)
      | n1 :: ((n2 :: _) as l) -> 
          if n1 <> n2 then
            fprintf ff "@[%s --> %s@ %a@]" 
              (Ident.source n1) (Ident.source n2) (print first) l
          else print first ff l in
  match l with | [] -> () | first :: _ -> print first ff l

(** Print a signature *)
let print_signature ff (p_args, c) =
  fprintf ff "@[%a -> %a@]" Printer.pattern_list p_args print_constraint c

let print_declaration ff f tys = 
  fprintf ff "@[val %s : %a@.@]" f print_signature tys  

let message loc (c, l) =
  eprintf "%aCausality error: the following constraint is not \
           causal.%a@.Here is an example of a cycle:@,[%a]@."
    output_location loc
    print_constraint c
    print_cycle l;
  raise Misc.Error

let cempty = Cempty
let is_empty c = (c = cempty)

let cand c1 c2 =
  match c1, c2 with
  | Cempty, _ -> c2 | _, Cempty -> c1
  | c1, c2 -> Cand(c1, c2)
let rec candlist l =
  match l with
  | [] -> Cempty
  | c1 :: l -> cand c1 (candlist l)

let cor c1 c2 =
  match c1, c2 with
  | Cempty, c2 -> c2
  | c1, Cempty -> c1
  | _ -> Cor(c1, c2)
let rec corlist l =
  match l with
  | [] -> Cempty
  | [c1] -> c1
  | c1 :: l -> cor c1 (corlist l)

let cseq c1 c2 =
  match c1, c2 with
  | Cempty, _ -> c2
  | _, Cempty -> c1
  | c1, c2 -> Cseq(c1, c2)
let rec cseqlist l =
  match l with
  | [] -> Cempty
  | c1 :: l -> cseq c1 (cseqlist l)

let read x = Cread(x)
let lastread x = Clastread(x)
let cwrite x = Cwrite(x)

(* applying a function to an optional value *)
let opt f = function | None -> cempty | Some(x) -> f x

(* projection and restriction *)
let clear acc c =
  let rec clearec c =
    match c with
    | Cor(c1, c2) -> cor (clearec c1) (clearec c2)
    | Cand(c1, c2) -> cand (clearec c1) (clearec c2)
    | Cseq(c1, c2) -> cseq (clearec c1) (clearec c2)
    | Cwrite(id) | Cread(id) | Clastread(id) ->
        if S.mem id acc then Cempty else c
    | Cempty -> c in
  clearec c

(* building a dependence graph from a scheduling constraint *)
let build c =
  (* [depends_on node_list1 node_list2] makes that every [x1] in [node_list1] *)
  (* depends on every [x2] from [node_list2] *)
  let seq node_list1 node_list2 =
    let seq x1 node_list2 =
      List.iter (fun x2 -> Graph.add_depends x2 x1) node_list2 in
    List.iter (fun x1 -> seq x1 node_list2) node_list1 in
  
  let depends_on node_list1 node_list2 =
    let depends_on x1 node_list2 =
      List.iter (fun x2 -> if (Graph.containt x1 = Graph.containt x2) &&
	                      (not (x1.Graph.g_tag = x2.Graph.g_tag))
                           then Graph.add_depends x1 x2) node_list2 in
    List.iter (fun x1 -> depends_on x1 node_list2) node_list1 in
  
  (* make a copy of a list of nodes - replace names by fresh names *)
  let copy l = List.map (fun { g_containt = n } -> make n) l in 
  (* given a constraint [c] returns a pair [reads, writes] *)
  let rec make c =
    match c with
      | Cand(c1, c2) -> 
	  let r1, w1 = make c1 in
	  let r2, w2 = make c2 in
	  (* read variables from [r1] also depend on *)
	  (* write variable from [w2] *)
	  depends_on r1 w2;
	  (* read variables from [r2] also depend on *)
	  (* write variable from [w1] *)
	  depends_on r2 w1;
	  r1 @ r2, w1 @ w2
      | Cseq(c1, c2) ->
	  let r1, w1 = make c1 in
	  let r2, w2 = make c2 in
	  (* read variables from [r1] also depend on *)
	  (* write variable from [w2] *)
	  depends_on r1 w2;
	  (* read variables from [r2] also depend on *)
	  (* write variable from [w1] *)
	  depends_on r2 w1;
	  (* moreover write variable from [w2] must be *)
	  (* done after read from [r1] *)
	  seq r1 w2;
	  r1 @ r2, w1 @ w2
      | Cor(c1, c2) ->
	  let r1, w1 = make c1 in
	  let r2, w2 = make c2 in
	  let w = w1 @ w2 in
	  (* let w = copy w in
	  (* read variables from [r1] also depend on write variable from [w] *)
	  depends_on r1 w;
	  (* read variables from [r2] also depend on write variable from [w] *)
	  depends_on r2 w; *)
	  r1 @ r2, w			 
      | Cwrite(n) -> 
          let g = Graph.make n in
          [], [g]
      | Cread(n) -> 
          let g = Graph.make n in
          [g], []
      | Clastread _ | Cempty -> [], [] in
  let r, w = make c in
  Graph.graph r w

(* the main entry. *)
let check loc c =
  let g = build c in
  let cycle_opt = Graph.cycle g in
  match cycle_opt with
    | None -> ()
    | Some(l) -> message loc (c, l)
