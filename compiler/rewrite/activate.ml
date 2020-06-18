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

(* removing equations [der x = e init e0 reset z1 -> e1 | ... | zn -> en] *)

open Misc
open Location
open Ident
open Global
open Zelus
open Zaux
open Initial
open Types
open Deftypes

(* An equation: [der x = e1 init e0 reset z1 -> e1 | ... | zn -> en] *)
(* into: [init x = e0 *)
(*        and present (z1) -> do x = e1 done | ... end and der x = e] *)

let block_of_eq s pat e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQeq(pat, e))]; 
    b_loc = no_location; b_write = { Deftypes.empty with dv = s };
    b_env = Env.empty }

let block_of_der s x e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQder(x, e, None, []))]; 
    b_loc = no_location; 
    b_write = { Deftypes.empty with der = s }; b_env = Env.empty }
    
let block_spat_e_list s pat spat_e_list =
  List.map 
    (fun { p_cond = spat; p_body = e; p_env = env; p_zero = zero } ->
      { p_cond = spat;
        p_body = block_of_eq s pat e;
        p_env = env; p_zero = zero }) spat_e_list

let present s x spat_e_list e eq_list =
  let spat_b_list =
    block_spat_e_list s (varpat x Initial.typ_float) spat_e_list in
  (* only generate a present if [spat_b_list] is not empty *)
  match spat_b_list with
    | [] -> (eq_der x e) :: eq_list
    | _ -> (eqmake (EQpresent(spat_b_list, None))) :: (eq_der x e) :: eq_list

let der_present x e e0_opt spat_e_list eq_list =
  (* present z1 -> do x = e1 done | ... | zn -> do x = en done 
     and der x = e and init x = e0 *)
  let eq_list = 
    match e0_opt with
    | None -> eq_list
    | Some(e0) -> (eq_init x e0) :: eq_list in
  present (S.singleton x) x spat_e_list e eq_list  

let rec exp e =
  let desc = match e.e_desc with
    | Econst(i) -> Econst(i)
    | Econstr0(longname) -> Econstr0(longname)
    | Eglobal(longname) -> Eglobal(longname)
    | Eop(op, e_list) -> Eop(op, List.map exp e_list)
    | Elocal(name) -> Elocal(name)
    | Elast(name) -> Elast(name)
    | Etuple(e_list) -> Etuple(List.map exp e_list)
    | Econstr1(c, e_list) -> Econstr1(c, List.map exp e_list)
    | Eapp(app, e, e_list) ->
       Eapp(app, exp e, List.map exp e_list)
    | Erecord(label_e_list) ->
      Erecord(List.map (fun (label, e) -> (label, exp e)) label_e_list)
    | Erecord_access(e_record, longname) ->
       Erecord_access(exp e_record, longname)
    | Erecord_with(e_record, label_e_list) ->
       Erecord_with(exp e_record,
		    List.map (fun (label, e) -> (label, exp e)) label_e_list)
    | Etypeconstraint(e, ty) -> Etypeconstraint(exp e, ty)
    | Eseq(e1, e2) -> Eseq(exp e1, exp e2)
    | Eperiod { p_phase = p1; p_period = p2 } ->
       Eperiod { p_phase = Misc.optional_map exp p1; p_period = exp p2 }
    | Elet(l, e) -> Elet(local l, exp e)
    | Eblock(b, e) -> Eblock(block b, exp e)
    | Epresent _ | Ematch _ -> assert false in
  { e with e_desc = desc }

and local ({ l_eq = eq_list } as l) =
  { l with l_eq = equation_list eq_list }

and equation_list eq_list = List.fold_left equation [] eq_list

and equation eq_list ({ eq_desc = desc } as eq) =
  match desc with
    | EQeq(pat, e) -> 
        { eq with eq_desc = EQeq(pat, exp e) } :: eq_list
    | EQpluseq(n, e) -> 
        { eq with eq_desc = EQpluseq(n, exp e) } :: eq_list
    | EQinit(n, e) ->
       { eq with eq_desc = EQinit(n, exp e) } :: eq_list
    | EQnext(n, e, e0_opt) ->
        { eq with eq_desc = 
		    EQnext(n, exp e, optional_map exp e0_opt) } :: eq_list
    | EQder(n, e, e0_opt, p_h_e_list) ->
        der_present n e e0_opt p_h_e_list eq_list
    | EQemit(name, e_opt) ->
       { eq with eq_desc =
		   EQemit(name, Misc.optional_map exp e_opt) } :: eq_list
    | EQmatch(total, e, m_h_list) ->
        { eq with eq_desc =
            EQmatch(total, exp e, 
                  List.map 
		    (fun ({ m_body = b } as m) -> { m with m_body = block b })
                    m_h_list) } :: eq_list
    | EQpresent(p_h_list, b_opt) ->
        { eq with eq_desc =
            EQpresent
	      (List.map (fun ({ p_cond = c; p_body = b } as p) ->
			 { p with p_cond = scondpat c; p_body = block b })
                 p_h_list,
               Misc.optional_map block b_opt) } :: eq_list
    | EQreset(res_eq_list, e) ->
       { eq with eq_desc =
		   EQreset(equation_list res_eq_list, exp e) } :: eq_list
    | EQand(and_eq_list) ->
       { eq with eq_desc = EQand(equation_list and_eq_list) } :: eq_list
    | EQbefore(before_eq_list) ->
       { eq with eq_desc = EQbefore(equation_list before_eq_list) } :: eq_list
    | EQblock(b_eq_list) -> 
       { eq with eq_desc = EQblock(block b_eq_list) } :: eq_list
    | EQforall ({ for_index = i_list; for_init = init_list;
		  for_body = b_eq_list } as body) ->
       let index ({ desc = desc } as ind) =
	 let desc = match desc with
	   | Einput(x, e) -> Einput(x, exp e)
	   | Eoutput _ -> desc
	   | Eindex(x, e1, e2) -> Eindex(x, exp e1, exp e2) in
	 { ind with desc = desc } in
       let init ({ desc = desc } as ini) =
	 let desc = match desc with
	   | Einit_last(x, e) -> Einit_last(x, exp e) in
	 { ini with desc = desc } in
       let i_list = List.map index i_list in
       let init_list = List.map init init_list in
       let b_eq_list = block b_eq_list in
       { eq with eq_desc = EQforall { body with for_index = i_list;
						for_init = init_list;
						for_body = b_eq_list } } ::
	 eq_list  
    | EQautomaton _ -> assert false

and block ({ b_locals = locals; b_body = eq_list } as b) =
  { b with b_locals = List.map local locals; b_body = equation_list eq_list }

and scondpat ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     { scpat with desc = Econdand(scondpat scpat1, scondpat scpat2) }
  | Econdor(scpat1, scpat2) ->
     { scpat with desc = Econdor(scondpat scpat1, scpat2) }
  | Econdexp(e) ->
     { scpat with desc = Econdexp(exp e) }
  | Econdpat(e, p) ->
     { scpat with desc = Econdpat(exp e, p) }
  | Econdon(scpat, e) ->
     { scpat with desc = Econdon(scondpat scpat, exp e) }

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> impl
    | Econstdecl(n, is_static, e) ->
       { impl with desc = Econstdecl(n, is_static, exp e) }
    | Efundecl(n, ({ f_body = e } as body)) ->
        { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
