(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* removing every statements *)
open Misc
open Location
open Ident
open Global
open Zelus
open Initial
open Types
open Deftypes

(* An equation: [pat = present z1 -> e1 | ... | zn -> en init e0] *)
(* is translated into: *)
(* [present | (z1) -> do pat = e1 done | ... | (zn) -> do pat = en done] *)
(* [else do pat = e done end] *)
(* [and init pat = e0] *)
(* An equation: [der x = e1 init e0 reset z1 -> e1 | ... | zn -> en] *)
(* into: [der x = e] and [init x = e0 *)
(*        and present (z1) -> do x = e1 done | ... end] *)

let typ_float = Initial.typ_float

let varpat x = 
  { p_desc = Evarpat(x); p_loc = no_location; p_typ = typ_float }

let eqmake desc = { eq_desc = desc; eq_loc = no_location }

let block_of_eq s pat e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQeq(pat, e))]; 
    b_loc = no_location; b_write = { Total.empty with dv = s }; b_env = Env.empty }

let block_of_der s x e =
  { b_vars = []; b_locals = []; b_body = [eqmake (EQder(x, e, None, []))]; 
    b_loc = no_location; b_write = { Total.empty with dr = s }; b_env = Env.empty }

(* [init pat e0_opt eq_list] *)
(* returns an extended sequence of equations with an [init pat = e0] *)
(* concatenated to [eq_list] *)
let init pat e0 eq_list =
  eqmake(EQinit(pat, e0, None)) :: eq_list

let eq pat e_opt eq_list =
  match e_opt with | None -> eq_list | Some(e) -> (eqmake(EQeq(pat, e))) :: eq_list

let der x e eq_list = (eqmake(EQder(x, e, None, []))) :: eq_list

let block_spat_e_list s pat spat_e_list =
  List.map 
    (fun { p_cond = spat; p_body = e } ->
      { p_cond = spat;
        p_body = block_of_eq s pat e;
        p_env = Env.empty }) spat_e_list

let present pat spat_e_list eq_list =
  let s = Vars.fv_pat S.empty pat in
  let spat_b_list = block_spat_e_list s pat spat_e_list in
  (* only generate a present if [spat_b_list] is not empty *)
  match spat_b_list with
    | [] -> eq_list
    | _ -> eqmake (EQpresent(spat_b_list, None)) :: eq_list

let present_and_initialize pat spat_e_list e0 eq_list =
  let eq_list = init pat e0 eq_list in
  present pat spat_e_list eq_list

let derpresent x e e0_opt spat_e_list eq_list =
  (* present z1 -> do x = e1 done | ... | zn -> do x = en done *)
  let eq_list = present (varpat x) spat_e_list eq_list in
  (* [der x = e] or [der x = e] and [init x = e0] *)
  let eq_list = (eqmake (EQder(x, e, None, []))) :: eq_list in
  match e0_opt with
    | None -> eq_list
    | Some(e0) -> init (varpat x) e0 eq_list

let rec exp e =
  let desc = match e.e_desc with
    | Econst(i) -> Econst(i)
    | Econstr0(longname) -> Econstr0(longname)
    | Eglobal(longname) -> Eglobal(longname)
    | Elocal(name) -> Elocal(name)
    | Elast(name) -> Elast(name)
    | Etuple(e_list) -> Etuple(List.map exp e_list)
    | Eapp(Etest, e_list) -> Eapp(Eop (Lident.Name "snd"), List.map exp e_list)
    | Eapp(op, e_list) -> Eapp(op, List.map exp e_list)
    | Erecord(label_e_list) ->
      Erecord(List.map (fun (label, e) -> (label, exp e)) label_e_list)
    | Erecord_access(e, longname) -> Erecord_access(exp e, longname)
    | Etypeconstraint(e, ty) -> Etypeconstraint(exp e, ty)
    | Eseq(e1, e2) -> Eseq(exp e1, exp e2)
    | Eperiod(p) -> Eperiod(p)
    | Elet(l, e) -> Elet(local l, exp e)
    | Epresent _ | Ematch _ -> assert false in
  { e with e_desc = desc }

and local ({ l_eq = eq_list } as l) =
  { l with l_eq = equation_list eq_list }

and equation_list eq_list = List.fold_left equation [] eq_list

and equation eq_list ({ eq_desc = desc } as eq) =
  match desc with
    | EQreset(b, e) ->
        { eq with eq_desc = EQreset(block b, exp e) } :: eq_list
    | EQeq(pat, e) -> 
        { eq with eq_desc = EQeq(pat, exp e) } :: eq_list
    | EQinit(pat, e0, Some({ e_desc = Epresent(p_h_e_list, None) })) -> 
        present_and_initialize pat p_h_e_list e0 eq_list
    | EQinit(pat, e0, e_opt) -> 
        { eq with eq_desc = EQinit(pat, exp e0, optional_map exp e_opt) } :: eq_list
    | EQnext(pat, e, e0_opt) ->
        { eq with eq_desc = EQnext(pat, exp e, optional_map exp e0_opt) } :: eq_list
    | EQder(n, e, e0_opt, p_h_e_list) ->
        derpresent n e e0_opt p_h_e_list eq_list
    | EQemit(name, e_opt) ->
        { eq with eq_desc = EQemit(name, Misc.optional_map exp e_opt) } :: eq_list
    | EQmatch(total, e, m_h_list) ->
        { eq with eq_desc =
            EQmatch(total, exp e, 
                  List.map 
		    (fun ({ m_body = b } as m) -> { m with m_body = block b })
                    m_h_list) } :: eq_list
    | EQpresent(p_h_list, b_opt) ->
        { eq with eq_desc =
            EQpresent
	      (List.map (fun ({ p_body = b } as p) -> { p with p_body = block b })
                 p_h_list,
               Misc.optional_map block b_opt) } :: eq_list
    | EQautomaton _ -> assert false

and block ({ b_locals = locals; b_body = eq_list } as b) =
  { b with b_locals = List.map local locals; b_body = equation_list eq_list }

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> impl
    | Econstdecl(n, e) -> { impl with desc = Econstdecl(n, exp e) }
    | Efundecl(n, ({ f_body = e } as body)) ->
        { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list

