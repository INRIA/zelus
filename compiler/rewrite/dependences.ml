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

(* dependences between equations *)
open Zelus
open Graph
   
type 'a collection =
  | And of 'a collection list (* parallel set of equations *)
  | Before of 'a collection list (* sequentiel set of equations *)
  | Leaf of 'a


(** Read/writes of an equation. *)
(* Control structures are treated as atomic blocks. Their set of write *)
(* variables is removed the set of read variables *)
let read ({ eq_write; eq_desc } as eq) =
  let last_acc, acc =
    Vars.fv_eq Ident.S.empty (Ident.S.empty, Ident.S.empty) eq in
  match eq_desc with
  | EQmatch(_, e, _) | EQreset(_, e) ->
      let w = Deftypes.names Ident.S.empty eq_write in
      let last_acc = Ident.S.diff last_acc w in
      let acc = Ident.S.diff acc w in
      Vars.fv Ident.S.empty (last_acc, acc) e
  | _ -> last_acc, acc
       
let def { eq_write = { Deftypes.dv = dv; Deftypes.di = di } } =
  (* derivatives are not taken into account *)
  Ident.S.union dv di

(** Initialization equations [init x = e] and reset [init x = e]... every ...] *)
let rec init { eq_desc = desc } =
  match desc with
  | EQinit _ -> true
  | EQreset(eq_list, _) -> List.for_all init eq_list
  | _ -> false

let nodep ({ eq_desc }) =
  match eq_desc with
  | EQeq(_, { e_desc = Eop(Eup, _) })
  | EQder(_, _, None, []) -> true | _ -> false

let index { eq_index = i } = i
let unsafe = Unsafe.equation
               
(* associate a fresh index to every equation *)
let rec fresh i eqs =
  match eqs with
  | Leaf(eq) -> Leaf { eq with eq_index = i }, i+1
  | Before(eqs_list) ->
      let eqs_list, i = Misc.map_fold fresh i eqs_list in
      Before(eqs_list), i
  | And(eqs_list) ->
      let eqs_list, i = Misc.map_fold fresh i eqs_list in
      And(eqs_list), i

(* Given a collection of equations, computes the associations *)
(* [xtable] associates the set of equation indexes [...x... = e] to [x] *)
(* [itable] associates the set of equations indexes [init x = e] to [x] *)
(* [eq_info_list] builds the list [index, eq, defs(eq), read(eq), last(eq)] *)
let rec name_to_index (xtable, itable, eq_info_list) eqs =
  match eqs with
  | Leaf(eq) ->
      let i = index eq in
      let w = def eq in
      let lv, v = read eq in
      let eq_info_list = (i, eq, w, v, lv) :: eq_info_list in
      if nodep eq then xtable, itable, eq_info_list
      else
        let update x t =
          Ident.Env.update x
            (function None -> Some (S.singleton i)
                    | Some(set) -> Some(S.add i set)) t in
        let xtable, itable =
          Ident.S.fold
            (fun x (xtable, itable) ->
               if init eq then xtable, update x itable
               else update x xtable, itable) w (xtable, itable) in
        xtable, itable, eq_info_list
  | Before(eq_list) | And(eq_list) ->
      List.fold_left name_to_index (xtable, itable, eq_info_list) eq_list

(* Build the dependence graph according to read/writes *)
let make_read_write xtable itable eq_info_list =
  (* find nodes according to a variable *)
  let find x table = try Ident.Env.find x table with Not_found -> S.empty in
  (* add dependences according to equation with index [n] *)
  let rec make g (n, eq, w, v, lv) =
    let g = Graph.add n eq g in
    (* equation with index [n] must be scheduled *)
    (* - after an equation [init x = e] where [x in w], excluding itself *)
    let l =
      S.remove n
        (Ident.S.fold (fun x iw -> S.union (find x itable) iw) w S.empty) in
    let g = Graph.add_before l (S.singleton n) g in
    (* - after an equation [...x... = e] or [init x = e] where [x in v] *)
    let l =
      Ident.S.fold
        (fun x iw -> S.union (find x xtable) (S.union (find x itable) iw))
        v S.empty in
    let g = Graph.add_before l (S.singleton n) g in
    (* - before an equation [...x... = e] where [x in lv] excluding itself *)
    let l =
      S.remove n
        (Ident.S.fold (fun x iw -> S.union (find x xtable) iw) lv S.empty) in
     let g = Graph.add_before (S.singleton n) l g in
    (* - after an equation [init x = e] where [x in lv] excluding itself *)
    let l =
      S.remove n
        (Ident.S.fold (fun x iw -> S.union (find x itable) iw) lv S.empty) in
    let g = Graph.add_before l (S.singleton n) g in
    g in
  List.fold_left make Graph.empty eq_info_list

(* Add extra dependences due to unsafe operations *)
let make_unsafes xtable itable g eqs =
  let rec unsafes (g, uset) eqs =
    match eqs with
    | Leaf(eq) -> g, if unsafe eq then S.add (index eq) uset else uset
    | And(eqs_list) ->
        List.fold_left unsafes (g, uset) eqs_list
    | Before(eqs_list) ->
        let g, uset_of_eqs_list =
          List.fold_left
            (fun (g, uset) eqs ->
             let g, uset_of_eqs = unsafes (g, S.empty) eqs in
             Graph.add_before uset uset_of_eqs g,
             if S.is_empty uset_of_eqs then uset
             else uset_of_eqs) (g, S.empty) eqs_list in
        g, S.union uset uset_of_eqs_list in
  let g, _ = unsafes (g, S.empty) eqs in
  g

(* The main entry function. Build the dependence graph from a *)
(* set of equations *)
let make eqs =
  let eqs, _ = fresh 0 eqs in
  let xtable, itable, eq_info_list =
    name_to_index (Ident.Env.empty, Ident.Env.empty, []) eqs in
  let g = make_read_write xtable itable eq_info_list in
  let g = make_unsafes xtable itable g eqs in
  Graph.outputs g

(* Print a graph of equations *)
let print ff g = Graph.print Printer.equation ff g
    
