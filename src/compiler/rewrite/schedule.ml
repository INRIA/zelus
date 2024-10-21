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

(* static scheduling. Applied to normalized expressions and equations *)

open Zelus
open Graph
open Dependences
open Mapfold

(* builds a collection from an equation *)
let rec collection ({ eq_desc } as eq) =
  match eq_desc with
  | EQand { ordered; eq_list } ->
     let d_list = List.map collection eq_list in
     if ordered then Then(d_list) else And(d_list)
  | _ -> Leaf(eq)

(* scheduling *)
let schedule eq =
  let fusion g eq_list =
    (* possible overlapping between conditions *)
    let join eq1 eq2 =
      match eq1.eq_desc, eq2.eq_desc with
      | EQmatch { e = e1; handlers = m_h_list1 },
        EQmatch { e = e2; handlers = m_h_list2 } 
	when Control.candidate (e1, m_h_list1) (e2, m_h_list2) -> true
      | _ -> false in

    (* precedence relation *)
    let relation { eq_index = n1} { eq_index = n2 } =
      (Graph.is_before g n1 n2) || (Graph.is_before g n2 n1) in
  
    let rec recook = function
      | [] -> []
      | eq :: eq_list -> eq >> (recook eq_list)
                               
    and (>>) eq eq_list =
      try
        insert eq eq_list
      with
      | Not_found -> eq :: eq_list
	             
    and insert eq = function
      | [] -> raise Not_found
      | eq1 :: eq_list ->
          if relation eq eq1 then raise Not_found
	  else
            try
              eq1 :: (insert eq eq_list)
            with
            | Not_found ->
	        if join eq eq1 then eq :: eq1 :: eq_list
                else raise Not_found in
    recook eq_list in
    
  (* build the dependence graph *)
  let g = Dependences.make (collection eq) in
  try
    (* check that there is no cycle. This situation should not arrive *)
    Graph.acyclic g;
    (* schedule it *)
    let eq_list = Graph.topological g in
    let eq_list = List.rev (fusion g (List.rev (fusion g eq_list))) in
    Control.joinlist eq_list
  with
    Graph.Error(Cycle(n_list)) ->
    Format.eprintf 
      "@[Scheduling: unexpected cycle (equations cannot be scheduled)@]@.";
    Format.eprintf "@[%a@]" Dependences.print g;
    Format.eprintf "@[Cycle: %a@.@]"
      (Pp_tools.print_list_r
         (fun ff index -> Format.fprintf ff "%d" index) "{" "," "}") n_list;
    raise Misc.Error  

let leq_t funs acc leq =
  let { l_eq } as leq, acc = Mapfold.leq_t funs acc leq in
  let l_eq = Aux.seq (schedule l_eq) in
  { leq with l_eq }, acc

let block funs acc ({ b_vars; b_body } as b) =
  let b_vars, acc =
    Util.mapfold (Mapfold.vardec funs) acc b_vars in
  let b_body, acc = Mapfold.equation funs acc b_body in
  let b_body = Aux.seq (schedule b_body) in
  { b with b_vars; b_body }, acc

let program genv0 p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with leq_t; block; global_funs } in
  let p, _ = Mapfold.program_it funs genv0 p in
  p
