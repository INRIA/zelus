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

(* control optimization. Fusion of conditionals *)
open Zelus

(* equality *)
let equal e1 e2 =
  match e1.e_desc, e2.e_desc with
    | Econst(i), Econst(j) when i = j -> true
    | Evar(i), Evar(j) when i = j -> true
    | Elast { id = i }, Elast { id = j } when i = j -> true
    | _ -> false

let static_patterns h =
  let pattern { pat_desc = desc } =
    match desc with
      | Econstpat _ | Econstr0pat _ -> true | _ -> false in
  let handler { m_pat = p } = pattern p in
  List.for_all handler h

(* Candidate for fusion *)
let candidate (e1, m_h_list1) (e2, m_h_list2) =
  (equal e1 e2) && (static_patterns m_h_list1) && (static_patterns m_h_list2) 

let equalpat p1 p2 =
  match p1.pat_desc, p2.pat_desc with
    | Econstpat(i), Econstpat(j) when i = j -> true
    | Econstr0pat(i), Econstr0pat(j) when i = j -> true
    | _ -> p1 = p2

let rec find pat = function
  | [] -> raise Not_found
  | ({ m_pat; m_body } as m_h) :: m_h_list  ->
      if equalpat pat m_pat then m_body, m_h_list
      else let m_body, m_h_list = find pat m_h_list in m_body, m_h :: m_h_list

let rec join eq1 eq_list =
  match eq1, eq_list with
    | { eq_desc = EQmatch { is_total = i1; e = e1; handlers = m_h_list1 } },
      { eq_desc = EQmatch { is_total = i2; e = e2; handlers = m_h_list2 } }
      :: eq_list
          when (candidate (e1, m_h_list1) (e2, m_h_list2)) ->
       { eq1 with eq_desc = EQmatch {is_total = i1 && i2; e = e1;
                  handlers = joinhandlers m_h_list1 m_h_list2 } } ::
	    eq_list
    | eq1, _ -> eq1 :: eq_list

and joinhandlers m_h_list1 m_h_list2 =
  match m_h_list1 with
    | [] -> m_h_list2
    | ({ m_pat; m_body } as m_h) :: m_h_list1 ->
        let m_h, m_h_list2 =
          try 
	    let m_body2, m_h_list2 = find m_pat m_h_list2 in 
	    { m_h with m_body = Aux.eq_and m_body m_body2 }, m_h_list2
          with Not_found -> m_h, m_h_list2 in
	m_h :: joinhandlers m_h_list1 m_h_list2

let rec joinlist = function
  | [] -> []
  | eq :: eq_list -> join eq (joinlist eq_list)
