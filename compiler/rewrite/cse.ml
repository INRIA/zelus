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
(* common sub-expression. Very simple things. To make it complete *)
(* we should first translate into clock data-flow equations *)
(* For the moment, only equations of the form [y = pre(x)] are shared *)
(* cse must be applied on normalized and scheduled equations *)

open Misc
open Ident
open Zelus

(** Build the association table [pre(n) -> x] and substitution [x\y] *)
(** every time some equation [y = pre(n)] already exists *)
let build_table subst eq_list =
  let rec equation (table, subst, eq_list) eq =
    match eq.eq_desc with
      | EQeq({ p_desc = Evarpat(x) } as p, 
             ({ e_desc = Eapp(Eunarypre, [{ e_desc = Elocal(n) }]) } as e)) -> 
          begin try
                  let y = Env.find n table in
                  table, 
                  (* extends the substitution *)
                  Env.add x y subst,
                  { eq with eq_desc = EQeq(p, { e with e_desc = Elocal(y) }) }
                    :: eq_list            
            with 
              | Not_found ->
                  (* build [pre(n) -> x] if it does not exist already *)
                  Env.add n x table, subst, eq :: eq_list
          end
      | EQeq _ | EQset _ | EQinit _ | EQnext _ 
      | EQmatch _ | EQreset _ | EQder _ -> table, subst, eq :: eq_list
      | EQemit _ | EQautomaton _ | EQpresent _ | EQblock _ -> assert false
 and equation_list table subst eq_list =
    List.fold_left equation (table, subst, []) eq_list in
  let table, subst, eq_list = equation_list Env.empty subst eq_list in
  subst, eq_list

(* substitution *)
let rec exp subst e = 
  match e.e_desc with
    | Econst _ | Econstr0 _ | Eglobal _ | Elast _ -> e
    | Elocal(n) ->
        begin try { e with e_desc = Elocal(Env.find n subst) }
        with Not_found -> e end
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (exp subst) e_list) }
    | Eapp(op, e_list) ->
        { e with e_desc = Eapp(op, List.map (exp subst) e_list) }
    | Erecord(label_e_list) ->
        { e with e_desc = 
            Erecord(List.map (fun (l, e) -> l, exp subst e) label_e_list) }
    | Erecord_access(e1, longname) ->
        { e with e_desc = Erecord_access(exp subst e1, longname) }
    | Etypeconstraint(e1, ty) ->
        { e with e_desc = Etypeconstraint(exp subst e1, ty) }
    | Eseq(e1, e2) ->
        { e with e_desc = Eseq(exp subst e1, exp subst e2) }
    | Elet(l, e_let) ->
       (* lets are supposed to be normalized, i.e., no more *)
       (* stateful functions inside *)
       { e with e_desc = Elet(local subst l, exp subst e_let) }
    | Eperiod _ | Epresent _ | Ematch _ -> assert false
    
(* [equation subst eq = eq'] apply a substitution to eq. *)
and equation subst eq =
  match eq.eq_desc with
    | EQeq(pat, e) -> { eq with eq_desc = EQeq(pat, exp subst e) }
    | EQset(ln, e) -> { eq with eq_desc = EQset(ln, exp subst e) }
    | EQinit(n, e0) -> 
       { eq with eq_desc = EQinit(n, exp subst e0) }
    | EQnext(n, e, e_opt) -> 
       { eq with eq_desc = EQnext(n, exp subst e, 
				  Misc.optional_map (exp subst) e_opt) }
    | EQmatch(total, e, m_h_list) ->
        let e = exp subst e in
        let m_h_list = 
          List.map 
            (fun ({ m_body = b} as h) -> { h with m_body = block subst b }) 
            m_h_list in
        { eq with eq_desc = EQmatch(total, e, m_h_list) }
    | EQreset(res_eq_list, e) ->
        { eq with eq_desc = 
		    EQreset(List.map (equation subst) res_eq_list, exp subst e) }
    | EQder(n, e, None, []) -> 
       { eq with eq_desc = EQder(n, exp subst e, None, []) }
    | EQder _ | EQemit _ | EQautomaton _ 
    | EQpresent _ | EQblock _ -> assert false

and local subst ({ l_eq = eq_list } as l) =
  (* extends the association table *)
  let subst, eq_list = build_table subst eq_list in
  (* apply the substitution *)
  let eq_list = List.map (equation subst) eq_list in
  { l with l_eq = eq_list }

and block subst ({ b_body = eq_list } as b) =
  let subst, eq_list = build_table subst eq_list in
  let eq_list = List.map (equation subst) eq_list in
  { b with b_body = eq_list }

(** the main entry for expressions. Warning: [e] must be in normal form *)
and nexp subst e =
  match e.e_desc with
    | Elet(l, e1) ->
        let l = local subst l in
        let e1 = nexp subst e1 in
        { e with e_desc = Elet(l, e1) }
    | _ -> exp subst e
  
let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = nexp Env.empty e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
