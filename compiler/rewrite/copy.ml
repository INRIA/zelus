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

(* Elimination of atomic values copy variables [x = y], constants, globals *)
(* The transformation is applied after static scheduling and before *)
(* translation into sequential code *)

open Misc
open Ident
open Zelus
open Deftypes

(** atomic expressions - either immediate constants or variables *)
type value = | Vlocal of Ident.t | Vlast of Ident.t | Vconst of Zelus.desc
						    
type renaming =
    { rel: value Env.t; (* the substitution *)
      defs: S.t; (* names after which the substitution cannot be applied *)
    }

let empty = { rel = Env.empty; defs = S.empty }

(** Append a renaming with a new relation *)
let append new_rel ({ rel = rel } as renaming) =
  { renaming with rel = Env.append new_rel rel }
    
(** Apply the renaming recursively. If [rel = [n\n1, n1\n2]], then *)
(** [rename n rel] = n2 *)
(** A substitution [n\last m] is not performed when [m] belongs to [defs] *)
let rename n { rel = rel; defs = defs } =
  let rec rename n =
    try 
      let m = Env.find n rel in
      begin
	match m with
	| Vlocal m -> rename m
	| Vlast m -> if S.mem m defs then raise Not_found else Elast m
	| Vconst(edesc) -> edesc
      end
    with Not_found -> Elocal n in
  rename n

let rec size ({ rel = rel } as renaming) ({ desc = desc } as s) =
  try
    let s =
      match desc with
      | Sconst _ | Sglobal _ -> s
      | Sname(n) ->
         let n = Env.find n rel in
         begin match n with
         | Vlocal n -> { s with desc = Sname(n) }
         | _ -> raise Not_found
         end
      | Sop(op, s1, s2) ->
         { s with desc = Sop(op, size renaming s1, size renaming s2) } in
    s
  with
    Not_found -> s

let operator renaming op =
  match op with
  | Efby | Eunarypre | Eifthenelse 
    | Eminusgreater | Eup | Einitial | Edisc
    | Ehorizon | Etest | Eaccess | Eupdate | Econcat | Eatomic -> op
  | Eslice(s1, s2) -> Eslice(size renaming s1, size renaming s2)
                            
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
  | EQreset(eq_list, _)
  | EQand(eq_list)
  | EQbefore(eq_list) ->  List.fold_left build rel eq_list
  | EQeq _ | EQpluseq _ | EQnext _ | EQinit _ | EQmatch _ 
  | EQder(_, _, None, [])
  | EQforall _ | EQblock _ -> rel
  | EQautomaton _ | EQpresent _ | EQemit _ | EQder _ -> assert false

(** Expressions. Apply [renaming] to every sub-expression *)
let rec expression renaming ({ e_desc = desc } as e) =
  match desc with
  | Econst _ | Econstr0 _ | Eglobal _ | Elast _ -> e
  | Elocal(x) -> { e with e_desc = rename x renaming }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression renaming) e_list) }
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (expression renaming) e_list) }
  | Erecord(n_e_list) -> 
     { e with e_desc =
		Erecord(List.map (fun (ln, e) ->
				  (ln, expression renaming e)) n_e_list) }
  | Erecord_access(e_record, ln) ->
     { e with e_desc = Erecord_access(expression renaming e_record, ln) }
  | Erecord_with(e_record, n_e_list) -> 
     { e with e_desc =
		Erecord_with(expression renaming e_record,
			     List.map (fun (ln, e) ->
				       (ln, expression renaming e)) n_e_list) }
  | Eop(op, e_list) ->
     { e with e_desc = Eop(operator renaming op,
			   List.map (expression renaming) e_list) }
  | Eapp(app, e_op, e_list) ->
     let e_op = expression renaming e_op in
     let e_list = List.map (expression renaming) e_list in
     { e with e_desc = Eapp(app, e_op, e_list) }
  | Etypeconstraint(e1, ty) -> 
     { e with e_desc = Etypeconstraint(expression renaming e1, ty) }      
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(expression renaming e1, expression renaming e2) }
  | Elet(l, e_let) ->
     let renaming, l = local renaming l in
     { e with e_desc = Elet(l, expression renaming e_let) }
  | Eperiod _ | Epresent _ | Ematch _ | Eblock _ -> assert false
						
(** Local declarations *)
and local renaming ({ l_eq = eq_list } as l) =
  let rel = List.fold_left build Env.empty eq_list in
  let renaming = append rel renaming in
  let renaming, eq_list = equation_list renaming eq_list in
  renaming, { l with l_eq = eq_list }

(** renaming of equations *)
and equation ({ defs = defs } as renaming, eq_list)
	     ({ eq_desc = desc; eq_write = w } as eq) =
  let desc = match desc with
    | EQeq(p, e) -> EQeq(p, expression renaming e)
    | EQpluseq(x, e) -> EQpluseq(x, expression renaming e)
    | EQinit(x, e0) -> EQinit(x, expression renaming e0)
    | EQmatch(total, e, m_b_list) ->
       let rename ({ m_body = b } as m_h) =
         { m_h with m_body = block renaming b } in
       EQmatch(total, expression renaming e, List.map rename m_b_list)
    | EQder(x, e, None, []) ->
       EQder(x, expression renaming e, None, [])
    | EQreset(res_eq_list, e) ->
       let e = expression renaming e in
       let _, eq_list = equation_list renaming res_eq_list in
       EQreset(eq_list, e)
    | EQforall ({ for_index = i_list; for_init = init_list;
		  for_body = b_eq_list } as b) ->
       let index ({ desc = desc } as ind) =
	 let desc = match desc with
	   | Einput(i, e) -> Einput(i, expression renaming e)
	   | Eoutput _ -> desc
	   | Eindex(i, e1, e2) ->
	      Eindex(i, expression renaming e1, expression renaming e2) in
	 { ind with desc = desc } in
       let init ({ desc = desc } as i) =
	 let desc = match desc with
	   | Einit_last(i, e) -> Einit_last(i, expression renaming e) in
	 { i with desc = desc } in
       let i_list = List.map index i_list in
       let init_list = List.map init init_list in
       let b_eq_list = block renaming b_eq_list in
       EQforall { b with for_index = i_list; for_init = init_list;
			 for_body = b_eq_list }
    | EQbefore(before_eq_list) ->
       let _, before_eq_list = equation_list renaming before_eq_list in
       EQbefore(before_eq_list)
    | EQand _ | EQblock _ | EQautomaton _ | EQpresent _ 
    | EQemit _ | EQder _ | EQnext _ -> assert false in
  { renaming with defs = Deftypes.cur_names defs w },
  { eq with eq_desc = desc } :: eq_list

and equation_list renaming eq_list =
  let renaming, eq_list = List.fold_left equation (renaming, []) eq_list in
  renaming, List.rev eq_list

and block renaming ({ b_body = eq_list } as b) =
  let rel = List.fold_left build Env.empty eq_list in
  let renaming = append rel renaming in
  let _, eq_list = equation_list renaming eq_list in
  { b with b_body = eq_list }

let implementation impl =
  match impl.desc with
    | Efundecl(f, ({ f_body = e } as body)) ->
        let e = expression empty e in
        let body = { body with f_body = e } in
        { impl with desc = Efundecl(f, body) }
    | _ -> impl
        
let implementation_list impl_list = Misc.iter implementation impl_list
