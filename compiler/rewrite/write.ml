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
(* compute write variables for every block. Done on normalized equations *)

open Ident
open Zelus
open Deftypes
 
let rec equation acc { eq_desc = desc } =
  match desc with
    | EQeq(pat, _) | EQinit(pat, _, _) | EQnext(pat, _, _) -> Vars.fv_pat acc pat
    | EQmatch(_, _, m_h_list) ->
        List.fold_left (fun acc { m_body = b } -> block acc b) acc m_h_list
    | EQreset(b, _) ->  block acc b
    | EQder _ -> acc
    | EQemit _ | EQpresent _ 
    | EQautomaton _ -> assert false
    
and equation_list acc eq_list = List.fold_left equation acc eq_list       
             
and block acc ({ b_vars = n_list; b_body = eq_list } as b) =
  let bounded = List.fold_left (fun acc n -> S.add n acc) S.empty n_list in
  let w = equation_list S.empty eq_list in
  let w = S.diff w bounded in
  b.b_write <- { Total.empty with dv = w };
  S.union acc w

and local { l_eq = eq_list } = ignore (equation_list S.empty eq_list)

let expression { e_desc = desc } =
  match desc with
    | Elet(l, e) -> local l
    | _ -> ()

let implementation impl =
  match impl.desc with
    | Efundecl(_, { f_body = e }) -> expression e; impl
    | _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list
