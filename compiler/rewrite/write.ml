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
(* compute write variables for every equation and block. *)

open Ident
open Zelus
open Deftypes

let rec equation ({ eq_desc = desc } as eq) =
  let defnames = match desc with
    | EQeq(pat, _) ->
        { Deftypes.empty with dv = Vars.fv_pat S.empty S.empty pat }	
    | EQnext(n, _, _) | EQemit(n, _) -> 
        { Deftypes.empty with dv = S.singleton n }
    | EQset _ -> Deftypes.empty
    | EQder(n, _, _, _) -> { Deftypes.empty with der = S.singleton n }
    | EQinit(n, _) -> { Deftypes.empty with di = S.singleton n }
    | EQmatch(_, _, m_h_list) ->
        List.fold_left
	  (fun acc { m_body = b } -> block acc b) Deftypes.empty m_h_list
    | EQreset(eq_list, _) -> equation_list Deftypes.empty eq_list
    | EQblock(b) -> block Deftypes.empty b
    | EQpresent _ | EQautomaton _ -> assert false in
  (* set the names defined in the equation *)
  eq.eq_write <- defnames;
  defnames
    
and equation_list acc eq_list = 
  List.fold_left (fun acc eq -> Total.union (equation eq) acc) acc eq_list       
             
and block acc ({ b_vars = n_list; b_body = eq_list } as b) =
  let bounded = List.fold_left (fun acc n -> S.add n acc) S.empty n_list in
  let { dv = dv; der = der; di = di } = equation_list Total.empty eq_list in
  let local_defnames = 
    { dv = S.diff dv bounded; 
      der = S.diff der bounded; di = S.diff di bounded } 
  in
  b.b_write <- local_defnames;
  Total.union acc local_defnames

and local { l_eq = eq_list } = ignore (equation_list Total.empty eq_list)

let expression { e_desc = desc } =
  match desc with
    | Elet(l, e) -> local l
    | _ -> ()

let implementation impl =
  match impl.desc with
    | Efundecl(_, { f_body = e }) -> expression e; impl
    | _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list
