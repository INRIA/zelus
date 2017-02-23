(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2017                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)

(* static scheduling. Applied to normalized expressions and equations *)

(* Apply the scheduling recursively to every expression *)
(* and equations. At the end, equations are scheduled so *)
(* that writes are done before write and state modifications *)
(* are performed after their read *)

open Zelus

module Dependences = Dependences.Make(Vars)

(* check the absence of cycles *)
let check_no_cycle g_list =
  let c_opt = Graph.cycle g_list in
  match c_opt with
  | None -> ()
  | Some(eq_list) ->
     Misc.internal_error
       "Cycle: equations cannot be scheduled"
       (Printer.equation_list "" "") eq_list
  
(* scheduling *)
let schedule eq_list =
  (* possible overlapping between conditions *)
  let join eq1 eq2 =
    match eq1.eq_desc, eq2.eq_desc with
      | EQmatch(_, e1, m_h_list1), EQmatch(_, e2, m_h_list2) 
	  when Control.candidate (e1, m_h_list1) (e2, m_h_list2) -> true
      | _ -> false in

  let rec recook = function
    | [] -> []
    | node :: node_list -> node >> (recook node_list)
      
  and (>>) node node_list =
    try
      insert node node_list
    with
      | Not_found -> node :: node_list
	  
  and insert node = function
    | [] -> raise Not_found
    | node1 :: node_list ->
        if Graph.linked node node1 then raise Not_found
	else
	  try
	    node1 :: (insert node node_list)
	  with
	    | Not_found ->
	        if join (Graph.containt node) (Graph.containt node1)
		then node :: node1 :: node_list
		else raise Not_found in
    
  (* build the dependence graph *)
  let graph = Dependences.build eq_list in
  (* check that there is no cycle. This situation should not arrive *)
  check_no_cycle graph;
  (* schedule it *)
  let l = Graph.topological graph in
  let l = List.rev (recook (List.rev (recook l))) in
  (* print *)
  let eq_list = List.map Graph.containt l in
  Control.joinlist eq_list

let rec equation ({ eq_desc = desc } as eq) =
  let desc = match desc with
    | EQeq _ | EQpluseq _ | EQinit _ | EQnext _ | EQder _ -> desc
    | EQmatch(total, e, p_h_list) ->
        EQmatch(total, e, 
		List.map 
                  (fun ({ m_body = b } as m_h) -> { m_h with m_body = block b })
                  p_h_list)
    | EQreset(eq_list, e) ->
       let eq_list = List.map equation eq_list in
       EQreset(schedule eq_list, e)
    | EQforall ({ for_body = b_eq_list } as body) ->
       let b_eq_list = block b_eq_list in
       EQforall { body with for_body = b_eq_list }
    | EQemit _ | EQautomaton _ | EQpresent _ | EQblock _ -> assert false in
  { eq with eq_desc = desc }
  
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
