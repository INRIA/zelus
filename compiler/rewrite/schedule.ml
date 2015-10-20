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
(* static scheduling *)

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

(** Apply the scheduling recursively to every expression *)
(** and equations. At the end, equations are scheduled so *)
(** that writes are done before write and state modifications *)
(** are performed after their read *)
(** Expressions *)
let rec exp e =
  match e.e_desc with
    | Econst _ | Econstr0 _ | Elocal _ | Elast _ | Eglobal _ -> e
    | Etuple(e_list) -> { e with e_desc = Etuple(List.map exp e_list) }
    | Eapp(op, e_list) -> { e with e_desc = Eapp(op, List.map exp e_list) }
    | Erecord(label_e_list) ->
        { e with e_desc = Erecord(List.map (fun (label, e) -> (label, exp e)) 
                                     label_e_list) }
    | Erecord_access(e, longname) -> 
        { e with e_desc = Erecord_access(exp e, longname) }
    | Etypeconstraint(e, ty) -> { e with e_desc = Etypeconstraint(exp e, ty) }
    | Elet(l, e_let) ->
        { e with e_desc = Elet(local l, exp e_let) }
    | Eseq(e1, e2) ->
        { e with e_desc = Eseq(exp e1, exp e2) }
    | Eperiod _ | Epresent _ | Ematch _ -> assert false
  
and equation ({ eq_desc = desc } as eq) =
  let desc = match desc with
    | EQeq _ | EQinit _ | EQnext _ | EQder _ -> desc
    | EQmatch(total, e, p_h_list) ->
        EQmatch(total, exp e, 
		List.map 
                  (fun ({ m_body = b } as m_h) -> { m_h with m_body = block b })
                  p_h_list)
    | EQreset(eq_list, e) -> EQreset(schedule eq_list, exp e)
    | EQblock(b) -> EQblock(block b)
    | EQemit _ | EQautomaton _ 
    | EQpresent _ -> assert false in
  { eq with eq_desc = desc }
  
and block ({ b_locals = l_list; b_body = eq_list } as b) =
  let l_list = List.map local l_list in
  (* schedule every nested block structure *)
  let eq_list = List.map equation eq_list in
  (* schedule the set of equations *)
  let eq_list = schedule eq_list in
  { b with b_locals = l_list; b_body = eq_list }

and local ({ l_eq = eq_list } as l) =
  (* translate and schedule the set of equations *)
  let eq_list = List.map equation eq_list in
  let eq_list = schedule eq_list in
  { l with l_eq = eq_list }

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
    | Efundecl(n, ({ f_body = e } as body)) ->
        { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
