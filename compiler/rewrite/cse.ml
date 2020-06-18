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

(* common sub-expression for registers. Very simple things. *)
(* For the moment, only equations of the form *)
(* [init x = e0 ... x = e] are shared *)

open Misc
open Ident
open Zelus

(** Build the association table [pre(n) -> x] and substitution [x\y] *)
(** every time some equation [y = pre(n)] already exists *)
let build_table subst eq_list =
  let rec equation (table, subst, eq_list) eq =
    match eq.eq_desc with
    | EQeq({ p_desc = Evarpat(x) } as p, 
           ({ e_desc = Eop(Eunarypre, [{ e_desc = Elocal(n) }]) } as e)) -> 
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
    | EQand(and_eq_list) ->
       let table, subst, and_eq_list = equation_list table subst and_eq_list in
       table, subst, { eq with eq_desc = EQand(and_eq_list) } :: eq_list
    | EQbefore(and_eq_list) ->
       let table, subst, and_eq_list = equation_list table subst and_eq_list in
       table, subst, { eq with eq_desc = EQbefore(and_eq_list) } :: eq_list
    | EQeq _ | EQpluseq _ | EQinit _ | EQnext _ 
    | EQmatch _ | EQreset _ | EQder _ | EQblock _ | EQforall _ ->
					 table, subst, eq :: eq_list
    | EQemit _ | EQautomaton _ | EQpresent _ -> assert false
  and equation_list table subst eq_list =
    let table, subst, eq_list =
      List.fold_left equation (table, subst, []) eq_list in
    table, subst, List.rev eq_list in
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
  | Econstr1(c, e_list) ->
     { e with e_desc = Econstr1(c, List.map (exp subst) e_list) }
  | Eop(op, e_list) ->
     let e_list = List.map (exp subst) e_list in
     { e with e_desc = Eop(op, e_list) }
  | Eapp(app, e_op, e_list) ->
     { e with e_desc =
		Eapp(app, exp subst e_op, List.map (exp subst) e_list) }
  | Erecord(label_e_list) ->
     { e with e_desc = 
		Erecord(List.map (fun (l, e) -> l, exp subst e) label_e_list) }
  | Erecord_access(e_record, longname) ->
     { e with e_desc = Erecord_access(exp subst e_record, longname) }
  | Erecord_with(e_record,label_e_list) ->
     { e with e_desc = 
		Erecord_with(exp subst e_record,
			     List.map
			       (fun (l, e) -> l, exp subst e) label_e_list) }
  | Etypeconstraint(e1, ty) ->
     { e with e_desc = Etypeconstraint(exp subst e1, ty) }
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(exp subst e1, exp subst e2) }
  | Eperiod _ | Epresent _ | Ematch _ | Elet _ | Eblock _ -> assert false
    
(* [equation subst eq = eq'] apply a substitution to eq. *)
and equation subst eq =
  match eq.eq_desc with
    | EQeq(pat, e) -> { eq with eq_desc = EQeq(pat, exp subst e) }
    | EQpluseq(n, e) -> { eq with eq_desc = EQpluseq(n, exp subst e) }
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
		    EQreset(List.map (equation subst) res_eq_list,
			    exp subst e) }
    | EQand(and_eq_list) ->
       { eq with eq_desc = EQand(List.map (equation subst) and_eq_list) }
    | EQbefore(before_eq_list) ->
       { eq with eq_desc = EQbefore(List.map (equation subst) before_eq_list) }
    | EQder(n, e, None, []) -> 
       { eq with eq_desc = EQder(n, exp subst e, None, []) }
    | EQblock(b) -> { eq with eq_desc= EQblock(block subst b) }
    | EQforall ({ for_index = i_list; for_init = init_list;
		  for_body = b_eq_list } as body) ->
       let index ({ desc = desc } as ind) =
	 let desc = match desc with
	   | Einput(x, e) -> Einput(x, exp subst e)
	   | Eoutput _ -> desc
	   | Eindex(x, e1, e2) -> Eindex(x, exp subst e1, exp subst e2) in
	 { ind with desc = desc } in
       let init ({ desc = desc } as ini) =
	 let desc = match desc with
	   | Einit_last(x, e) -> Einit_last(x, exp subst e) in
	 { ini with desc = desc } in
       let i_list = List.map index i_list in
       let init_list = List.map init init_list in
       let b_eq_list = block subst b_eq_list in
       { eq with eq_desc =
		   EQforall { body with for_index = i_list;
					for_init = init_list;
					for_body = b_eq_list } }
    | EQder _ | EQemit _ | EQautomaton _ | EQpresent _ -> assert false

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
let exp subst e =
  match e.e_desc with
    | Elet(l, e1) ->
        let l = local subst l in
        let e1 = exp subst e1 in
        { e with e_desc = Elet(l, e1) }
    | _ -> exp subst e
  
let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
         { impl with desc =
		       Efundecl(n, { body with f_body = exp Env.empty e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
