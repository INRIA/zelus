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
(* Elimination of atomic values copy variables [x = y], constants, globals *)
(* The transformation is applied after static scheduling and before *)
(* translation into sequential code *)

open Misc
open Ident
open Zelus
open Deftypes

(** atomic expressions - either immediate constants or variables *)
type value = | Vlocal of Ident.t | Vlast of Ident.t | Vconst of Zelus.desc
						    
type renaming = value Env.t (* the substitution *)
                      
(** Closure of a relation. If [x1\x2, x2\x3] => [x1\x3, x2\x3] *)
(* The implementation is poor: we should replace it by union-find *)
let closure rel = 
  (* [closure rel n = rel, m] returns a new renaming and *)
  (* the associated name [m] to [n] so that there is no link [m\k] *)
  let rec closure v =
    match v with
    | Vconst _ | Vlast _ -> v
    | Vlocal(x) -> try closure (Env.find x rel) with Not_found -> v in
  Env.fold (fun n v acc -> Env.add n (closure v) acc) rel Env.empty

(* remove entries of the form [x\last y] *)
let remove_last rel =
  let not_last _ v =
    match v with | Vlast _ -> false | Vconst _ | Vlocal _ -> true in
  Env.filter not_last rel
	     
(** Apply the renaming *)
let rename n rel =
  try 
    let m = Env.find n rel in
    begin
      match m with
      | Vlocal m -> Elocal m
      | Vlast m -> Elast m
      | Vconst(edesc) -> edesc
    end
  with Not_found -> Elocal n

(** Build a substitution [x1\v1,...,xn\vn]. *)
let rec build rel { eq_desc = desc } =
  match desc with
  | EQeq({ p_desc = Evarpat(x) }, { e_desc = desc }) ->
     let rel =
       match desc with
       | Elocal m -> Env.add x (Vlocal(m)) rel
       | Eglobal _ | Econst _ -> Env.add x (Vconst(desc)) rel
       | Elast m -> Env.add x (Vlast(m)) rel
       | _ -> rel in
     rel
  | EQeq _ | EQset _ | EQnext _ | EQinit _ | EQmatch _ | EQreset _ 
  | EQder(_, _, None, []) | EQblock _ -> rel
  | EQautomaton _ | EQpresent _ | EQemit _ | EQder _ -> assert false

(** Expressions. Apply [rel] to every sub-expression *)
let rec expression rel ({ e_desc = desc } as e) =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ | Elast _ -> e
  | Elocal(x) -> { e with e_desc = rename x rel }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression rel) e_list) }
  | Erecord(n_e_list) -> 
     { e with e_desc =
		Erecord(List.map (fun (ln, e) ->
				  (ln, expression rel e)) n_e_list) }
  | Erecord_access(e, ln) ->
     { e with e_desc =
		Erecord_access(expression rel e, ln) }
  | Eapp(op, e_list) ->
     { e with e_desc = Eapp(op, List.map (expression rel) e_list) }
  | Etypeconstraint(e1, ty) -> 
     { e with e_desc = Etypeconstraint(expression rel e1, ty) }      
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(expression rel e1, expression rel e2) }
  | Elet(l, e_let) ->
     let rel, l = local rel l in
     { e with e_desc = Elet(l, expression (remove_last rel) e_let) }
  | Eperiod _ | Epresent _ | Ematch _ -> assert false
						
(** Local declarations *)
and local rel ({ l_eq = eq_list } as l) =
  let rel = List.fold_left build rel eq_list in
  let rel = closure rel in
  rel, { l with l_eq = equation_list rel eq_list }

(** rel of equations *)
and equation rel ({ eq_desc = desc } as eq) =
  let desc = match desc with
    | EQeq(p, e) -> EQeq(p, expression rel e)
    | EQset(ln, e) -> EQset(ln, expression rel e)
    | EQinit(x, e0) -> EQinit(x, expression rel e0)
    | EQmatch(total, e, m_b_list) ->
       let rename ({ m_body = b } as m_h) =
         { m_h with m_body = block rel b } in
       EQmatch(total, expression rel e, List.map rename m_b_list)
    | EQder(x, e, None, []) ->
       EQder(x, expression rel e, None, [])
    | EQreset(res_eq_list, e) ->
       let e = expression rel e in
       EQreset(equation_list rel res_eq_list, e)
    | EQblock _ | EQautomaton _ | EQpresent _ 
    | EQemit _ | EQder _ | EQnext _ -> assert false in
  { eq with eq_desc = desc }

and equation_list rel eq_list = List.map (equation rel) eq_list

and block rel ({ b_body = eq_list } as b) =
  let rel = List.fold_left build rel eq_list in
  let rel = closure rel in
  { b with b_body = equation_list rel eq_list }

let implementation impl =
  match impl.desc with
    | Efundecl(f, ({ f_body = e } as body)) ->
        let e = expression Env.empty e in
        let body = { body with f_body = e } in
        { impl with desc = Efundecl(f, body) }
    | _ -> impl
        
let implementation_list impl_list = Misc.iter implementation impl_list
