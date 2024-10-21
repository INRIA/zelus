(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* dependences between equations *)
open Zelus
open Ident
open Defnames
open Graph
open Vars

type 'a collection =
  | And of 'a collection list (* parallel set of equations *)
  | Then of 'a collection list (* sequentiel set of equations *)
  | Leaf of 'a

let fv_eq eq = Vars.equation eq
let fv { lv; v } e = Vars.expression { lv; v } e

(* Read/writes of an equation. *)
(* Control structures are treated as atomic blocks. Their set of write *)
(* variables is removed from the set of read variables *)
let read ({ eq_write; eq_desc } as eq) =
  let open Ident in
  let { lv; v } = fv_eq eq in
  match eq_desc with
  | EQmatch { e } | EQif { e } | EQreset(_, e) ->
      let w = Defnames.names S.empty eq_write in
      let lv = S.diff lv w in
      let v = S.diff v w in
      fv { lv; v } e
  | EQlocal _ | EQlet _ ->
      let w = Defnames.names S.empty eq_write in
      let lv = S.diff lv w in
      let v = S.diff v w in
      { lv; v }
  | _ -> { lv; v }
       
let def { eq_write = { dv; di } } =
  (* derivatives are not taken into account *)
  Ident.S.union dv di

(* Initialization equations [init x = e] and *)
(* reset [init x = e]... every ...] *)
let rec init { eq_desc } =
  match eq_desc with
  | EQinit _ -> true
  | EQreset(eq, _) -> init eq
  | _ -> false

let nodep ({ eq_desc }) =
  match eq_desc with
  | EQeq(_, { e_desc = Eop(Eup, _) })
  | EQder { e_opt = None; handlers = [] } -> true | _ -> false

let index { eq_index } = eq_index
let unsafe { eq_safe } = not eq_safe 
               
(* associate a fresh index to every equation *)
let rec fresh i eqs =
  match eqs with
  | Leaf(eq) -> Leaf { eq with eq_index = i }, i+1
  | Then(eqs_list) ->
      let eqs_list, i = Util.mapfold fresh i eqs_list in
      Then(eqs_list), i
  | And(eqs_list) ->
      let eqs_list, i = Util.mapfold fresh i eqs_list in
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
      let { lv; v } = read eq in
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
  | Then(eq_list) | And(eq_list) ->
      List.fold_left name_to_index (xtable, itable, eq_info_list) eq_list

(* Build the dependence graph according to read/writes *)
let make_read_write xtable itable eq_info_list =
  (* find nodes according to a variable *)
  let find x table = try Env.find x table with Not_found -> S.empty in
  (* add dependences according to equation with index [n] *)
  let make g (n, eq, w, v, lv) =
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
    | Then(eqs_list) ->
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

(* for debug purposes *)
let dump ff eq_info_list =
  Pp_tools.print_list_r
    (fun ff (index, eq, w, v, lv) ->
      Format.fprintf ff "@[%d: %a (w: %a; v: %a; lv: %a)@]"
        index Printer.equation eq
        Ident.S.fprint_t w
        Ident.S.fprint_t v
        Ident.S.fprint_t lv)
    "" "" "" ff eq_info_list

(* The main entry function. Build the dependence graph from a *)
(* set of equations *)
let make eqs =
  let eqs, _ = fresh 0 eqs in
  let xtable, itable, eq_info_list =
    name_to_index (Env.empty, Env.empty, []) eqs in
  let g = make_read_write xtable itable eq_info_list in
  let g = make_unsafes xtable itable g eqs in
  if !Misc.debug then Format.eprintf "@[%a@.@]" dump eq_info_list;
  Graph.outputs g

(* Print a graph of equations *)
let print ff g = Graph.print Printer.equation ff g
    
