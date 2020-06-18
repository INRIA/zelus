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

(* control optimization. Fusion of conditionals *)
open Zelus
open Deftypes

(* equality *)
let equal e1 e2 =
  match e1.e_desc, e2.e_desc with
    | Econst(i), Econst(j) when i = j -> true
    | Elocal(i), Elocal(j) when i = j -> true
    | Elast(i), Elast(j) when i = j -> true
    | _ -> false

let static_patterns h =
  let pattern { p_desc = desc } =
    match desc with
      | Econstpat _ | Econstr0pat _ -> true | _ -> false in
  let handler { m_pat = p } = pattern p in
  List.for_all handler h

(* Candidate for fusion *)
let candidate (e1, m_h_list1) (e2, m_h_list2) =
  (equal e1 e2) && (static_patterns m_h_list1) && (static_patterns m_h_list2) 

let equalpat p1 p2 =
  match p1.p_desc, p2.p_desc with
    | Econstpat(i), Econstpat(j) when i = j -> true
    | Econstr0pat(i), Econstr0pat(j) when i = j -> true
    | _ -> p1 = p2

let rec find p = function
  | [] -> raise Not_found
  | ({ m_pat = po; m_body = b } as m_h) :: m_h_list  ->
      if equalpat p po then b, m_h_list
      else let b, m_h_list = find p m_h_list in b, m_h :: m_h_list

let rec join eq1 eq_list =
  match eq1, eq_list with
    | { eq_desc = EQmatch(is_total1, e1, m_h_list1) },
      { eq_desc = EQmatch(is_total2, e2, m_h_list2) } :: eq_list
          when (candidate (e1, m_h_list1) (e2, m_h_list2)) ->
        { eq1 with eq_desc = EQmatch(ref (!is_total1 && !is_total2), e1, 
				     joinhandlers m_h_list1 m_h_list2) } ::
	    eq_list
    | eq1, _ -> eq1 :: eq_list

and joinhandlers m_h_list1 m_h_list2 =
  match m_h_list1 with
    | [] -> m_h_list2
    | ({ m_pat = po; m_body = bo } as m_h) :: m_h_list1 ->
        let m_h, m_h_list2 =
          try 
	    let b, m_h_list2 = find po m_h_list2 in 
	    { m_h with m_body = joinblock bo b }, m_h_list2
          with Not_found -> m_h, m_h_list2 in
	m_h :: joinhandlers m_h_list1 m_h_list2

and joinblock
    ({ b_vars = n_list1; b_locals = l1; b_body = eq_list1;
       b_env = b_env1; b_write = { dv = w1 } } as b1)
    { b_vars = n_list2; b_locals = l2; b_body = eq_list2;
      b_env = b_env2; b_write = { dv = w2 } } =
  { b1 with b_vars = n_list1 @ n_list2;
    b_locals = l1 @ l2; b_body = eq_list1 @ eq_list2;
    b_write = { Deftypes.empty with dv = Ident.S.union w1 w2 } }
  
let rec joinlist = function
  | [] -> []
  | eq :: eq_list -> join eq (joinlist eq_list)
