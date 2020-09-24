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

(* static scheduling. Applied to normalized expressions and equations *)

open Zelus
open Graph
open Dependences

(* builds a collection from an equation *)
let collection eq_list =
  let rec collection ({ eq_desc } as eq) =
    match eq_desc with
    | EQand(and_eq_list) -> And(List.map collection and_eq_list)
    | EQbefore(before_eq_list) -> Before(List.map collection before_eq_list)
    | _ -> Leaf(eq) in
  And(List.map collection eq_list)

(* scheduling *)
let schedule eq_list =
  let fusion g eq_list =
    (* possible overlapping between conditions *)
    let join eq1 eq2 =
      match eq1.eq_desc, eq2.eq_desc with
      | EQmatch(_, e1, m_h_list1), EQmatch(_, e2, m_h_list2) 
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
  let g = Dependences.make (collection eq_list) in
  try
    (* check that there is no cycle. This situation should not arrive *)
    Graph.acyclic g;
    (* schedule it *)
    let eq_list = Graph.topological g in
    let eq_list = List.rev (fusion g (List.rev (fusion g eq_list))) in
    Control.joinlist eq_list
  with
    Graph.Error(Cycle(n_list)) ->
      Misc.internal_error
       "Unexpected cycle: equations cannot be scheduled"
       (Printer.equation_list "" "") eq_list
  

let rec equation ({ eq_desc } as eq) =
  match eq_desc with
  | EQeq _ | EQpluseq _ | EQinit _ | EQnext _ | EQder _ -> eq
  | EQmatch(total, e, p_h_list) ->
     { eq with eq_desc = match_eq total e p_h_list }
  | EQreset(res_eq_list, e) ->
     { eq with eq_desc = reset_eq res_eq_list e }
  | EQand(and_eq_list) ->
     { eq with eq_desc = EQand(List.map equation and_eq_list) }
  | EQbefore(before_eq_list) ->
     { eq with eq_desc = EQbefore(List.map equation before_eq_list) }
  | EQforall(body) ->
     { eq with eq_desc = forall_eq body }
  | EQemit _ | EQautomaton _ | EQpresent _ | EQblock _ -> assert false

and match_eq total e p_h_list =
  EQmatch(total, e,
          List.map (fun ({ m_body = b } as m_h) ->
	      { m_h with m_body = block b }) p_h_list)

and reset_eq res_eq_list e =
  let res_eq_list = List.map equation res_eq_list in
  EQreset(schedule res_eq_list, e)

and forall_eq ({ for_body = b_eq_list } as body) =
  let b_eq_list = block b_eq_list in
  EQforall { body with for_body = b_eq_list }
  
and block ({ b_body = eq_list } as b) =
  (* schedule every nested equation *)
  let eq_list = List.map equation eq_list in
  (* schedule the set of equations *)
  let eq_list = schedule eq_list in
  { b with b_body = eq_list }

and local ({ l_eq = eq_list } as l) =
  (* translate and schedule the set of equations *)
  let eq_list = List.map equation eq_list in
  let eq_list = schedule eq_list in
  { l with l_eq = eq_list }

(** Top level expressions *)
let exp ({ e_desc = desc } as e) =
  let desc =
    match desc with
    | Elet(l, e) -> Elet(local l, e)
    | _ -> desc in
  { e with e_desc = desc }
  
let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
    | Efundecl(n, ({ f_body = e } as body)) ->
        { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list


