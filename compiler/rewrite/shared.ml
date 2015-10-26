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
(* Identify assignments to shared variables and memories. *)
(* At the end, equations *)
(* on structured patterns like [pat = e] are such that no variable in [pat] *)
(* is shared nor a memory. At the end, all equations on those variables *)
(* are of the form [x = e] *)
open Location
open Ident
open Zelus
open Deftypes
open Zaux

(* Computes the set of memories, that is, variables with flag [last] *)
(* add it to [dv] *)
let memories dv l_env =
  let add x sort acc =
    match sort with | Sval | Svar _ -> acc
      | Smem { m_previous = last } -> if last then S.add x acc else acc in
  Env.fold (fun x { t_sort = sort } acc -> add x sort acc) l_env dv
    
(* makes a list of copies [x = x_copy] *)
(* and extends the local environment with definitions for the [x_copy] *)
let add_copies n_list n_env eq_list copies =
  (* makes a value for [x_copy] *)
  let value ty = { t_sort = Deftypes.value; t_typ = ty } in
  let n_env =
    Env.fold
      (fun x (x_copy, ty) acc -> Env.add x_copy (value ty) acc) copies n_env in
  let n_copy_list =
    Env.fold
      (fun _ (x_copy, ty) acc ->
	(Zaux.vardec_from_entry x_copy { t_sort = Sval; t_typ = ty }) :: acc)
      copies n_list in
 let eq_list =
    Env.fold
      (fun x (x_copy, ty) acc ->
       (eqmake (EQeq(varpat x ty, var x_copy ty))) :: acc) copies eq_list in
  n_copy_list, eq_list, n_env

(* makes a copy of a pattern if it contains a shared variable [x] *)
(* introduce auxilary equations [x = x_copy] in [copies] *)
let rec pattern dv copies pat =
  match pat.p_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> pat, copies
    | Etuplepat(p_list) ->
        let p_list, copies =
          List.fold_right 
            (fun p (p_list, copies) -> 
              let p, copies = pattern dv copies p in
              p :: p_list, copies) p_list ([], copies) in
        { pat with p_desc = Etuplepat(p_list) }, copies
    | Evarpat(n) -> 
        if S.mem n dv then
          let ncopy = Ident.fresh "copy" in
          { pat with p_desc = Evarpat(ncopy) },
	  Env.add n (ncopy, pat.p_typ) copies
        else pat, copies
    | Erecordpat(label_pat_list) ->
        let label_pat_list, copies =
          List.fold_right 
            (fun (label, p) (label_p_list, copies) -> 
              let p, copies = pattern dv copies p in
              (label, p) :: label_p_list, copies) label_pat_list ([], copies) in
        { pat with p_desc = Erecordpat(label_pat_list) }, copies
    | Etypeconstraintpat(p, ty) ->
        let p, copies = pattern dv copies p in
        { pat with p_desc = Etypeconstraintpat(p, ty) }, copies
    | Ealiaspat(p, n) ->
        let p, copies = pattern dv copies p in
        let n, copies = 
          if S.mem n dv then
            let ncopy = Ident.fresh "copy" in
            ncopy, Env.add n (ncopy, p.p_typ) copies
          else n, copies in
        { pat with p_desc = Ealiaspat(p, n) }, copies
    | Eorpat _ -> assert false

let rec exp e =
  let desc = match e.e_desc with
    | Econst _ | Econstr0 _ | Eglobal _ 
    | Elocal _ | Elast _ | Eperiod _ as desc -> desc
    | Etuple(e_list) -> Etuple(List.map exp e_list)
    | Eapp(op, e_list) -> Eapp(op, List.map exp e_list)
    | Erecord(label_e_list) ->
        Erecord(List.map (fun (label, e) -> (label, exp e)) label_e_list)
    | Erecord_access(e1, longname) ->
        Erecord_access(exp e1, longname)
    | Etypeconstraint(e1, ty) ->
        Etypeconstraint(exp e1, ty)
    | Elet(l, e_let) ->
        Elet(local l, exp e_let)
    | Eseq(e1, e2) ->
        Eseq(exp e1, exp e2)
    | Epresent _ | Ematch _ -> assert false in
  { e with e_desc = desc }

(* [dv] is the set of names possibly written in [eq] which are visible *)
(* outside of the block or are memories *)
and equation dv copies eq =
  match eq.eq_desc with
    | EQeq({ p_desc = Evarpat(n) } as pat, e) ->
       { eq with eq_desc = EQeq(pat, exp e) }, copies
    | EQeq(pat, e) ->
       (* if some variable from [pat] are shared, [pat] is renamed into [pat'] *)
       (* and auxiliary equations [x1 = x_copy1 and ... and xn = x_copyn] *)
       (* are added *)
       let pat, copies = pattern dv copies pat in
       { eq with eq_desc = EQeq(pat, exp e) }, copies
    | EQpluseq(n, e) ->
       { eq with eq_desc = EQpluseq(n, exp e) }, copies
    | EQder(n, e, None, []) ->
       { eq with eq_desc = EQder(n, exp e, None, []) }, copies
    | EQinit(n, e0) ->
       { eq with eq_desc = EQinit(n, exp e0) }, copies
    | EQmatch(total, e, m_h_list) ->
       let m_h_list =
         List.map
	   (fun ({ m_body = b } as handler) ->
	    { handler with m_body = block dv b } )
	   m_h_list in
       { eq with eq_desc = EQmatch(total, exp e, m_h_list) }, copies
    | EQreset(res_eq_list, e) ->
       let res_eq_list, copies = equation_list dv copies res_eq_list in
       { eq with eq_desc = EQreset(res_eq_list, exp e) }, copies
    | EQblock(b) ->
       let b = block dv b in
       { eq with eq_desc = EQblock(b) }, copies
    | EQemit _ | EQautomaton _ | EQpresent _ 
    | EQder _ | EQnext _ -> assert false

(* [dv] defines names modified by [eq_list] but visible outside of the block *)
and equation_list dv copies eq_list = 
  let equationrec (eq_list, copies) eq =
    let eq, copies = equation dv copies eq in
    eq :: eq_list, copies in
  List.fold_left equationrec ([], copies) eq_list
 
and local ({ l_eq = eq_list; l_env = l_env } as l) =
  let dv = memories S.empty l_env in
  let eq_list, copies = equation_list dv Env.empty eq_list in
  let _, eq_list, l_env = add_copies [] l_env eq_list copies in
  { l with l_eq = eq_list; l_env = l_env }
    
(* A variable [x] written by a block [b] is considered to be shared *)
(* when it is visible outside of the block, i.e., [x in dv_b] *)
(* Those variables and memories must be modified with equations of the *)
(* form [x = e] only. *)
and block dv
	  ({ b_vars = n_list; b_locals = l_list;
	     b_body = eq_list; b_write = ({ dv = dv_b } as names); 
	b_env = n_env } as b) =
  let dv_b = memories dv_b n_env in
  let eq_list, copies = equation_list (S.union dv dv_b) Env.empty eq_list in
  let n_list, eq_list, n_env = add_copies n_list n_env eq_list copies in
  let l_list = List.map local l_list in
  { b with b_vars = n_list; b_locals = l_list; b_body = eq_list; 
    b_write = names; b_env = n_env }

let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
