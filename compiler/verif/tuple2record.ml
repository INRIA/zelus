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

(* Rewrite tuples into records. *)

open Misc
open Zelus
open Zaux
open Ident
open Deftypes

(* a memoization table which associates a type name to a list of types names *)
(* used to avoid creating several definition of the same type *)
(* very limited stuff here: (t1 * t2) and (t2 * t1) will be associated to *)
(* two different type definitions. To be improved ! *)
module T =
  Map.Make
    (struct
      type t = name list
      let compare t1 t2 = Pervasives.compare t1 t2
    end)

type result = { ty_name: name;
                ty_labels: name list; }
              
type return =
  { def_types: (name * typ) Misc.Env.t;
    (* the list of declared record types: type t = { l1: t1;...; ln: tn } *)
    table: result T.t;
    (* inverse table: the type name and the list of labels *)
    (* associated to a tuple type (t1,..., tn) *)
  }

let empty = { def_types = Misc.Env.empty; hash_table = [] }

(** Return the record type associated to the tuple type [ty_list] *)
let recordtype ({ def_types = dtypes; table = table } as return) ty_list =
  let ty, l_list, return =
    try
      find ty_list table, return
    with
    | Not_found ->
        (* add a new type *)
        let l_list = List.map (fun _ -> Ident.fresh "l") ty_list in
        let l_ty_list =
          List.map2 (fun l ty -> (l, ty)) l_list ty_list in
        let ty_name = Ident.fresh "ty" in
        let dtypes = Misc.Env.add ty_name l_ty_list dtypes in
        let table = (ty_list, ty, l_list) :: table in
        ty_name, l_list, { def_types = dtypes; table = table } in
     Zaux.record l_list e_list ty

(* Translate a tuple into a record *)
let tuple_into_record return e_list =
  let ty_list = List.map (fun e -> e.e_typ) e_list in
  recordtype return ty_list

(* Translate a tuple into a record *)
let tuplepat_into_record return e_list =
  recordtype return ty_list

let rec pattern return ({ p_desc = desc } as p) =
  match desc with
  | Ewildpat | Econstpat _ | Econstr0pat _ | Evarpat _ -> p, return
  | Etuplepat(p_list) ->
      let p_list, return = Misc.map_fold pattern return p_list in
      tuplepat_into_recordpat return p_list
  | Etypeconstraintpat(p, ty) ->
      let p, return = pattern return p in
      { p with p_desc = Etypeconstraintpat(p, ty) }, return
  | Eorpat _ | Erecordpat _ -> assert false
  
(* translate expressions *)
let rec expression return ({ e_desc = desc } as e) =
  match desc with
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e, return 
  | Eapp(app, e_arg, e_list) ->
      let e_arg, return = expression return e_arg in
      let e_list, return = Misc.map_fold expression return e_list in
      { e with e_desc = Eapp(app, e_arg, e_list) }, return
  | Eop(op, e_list) ->
      let e_list, return = Misc.map_fold expression return e_list in
      { e with e_desc = Eop(op, e_list) }, return
  | Erecord_access(e, lid) ->
      let e, return = expression return e in
      { e with e_desc = Erecord_access(e, lid) }, return
  | Erecord(l_e_list) ->
      let l_e_list, return =
        Misc.map_fold
          (fun return (l, e) ->
             let e, return = expression return e in (l, e), return)
          return l_e_list in
      { e with e_desc = Erecord (l_e_list) }, return
  | Etypeconstraint(e, ty) ->
      let e, return = expression return e in
      { e with e_desc = Etypeconstraint(e, ty) }, return
  | Etuple(e_list) ->
      let e_list, return = Misc.map_fold expression return e_list in
      tuple_into_record return e_list
  | Ematch _ | Eseq _ | Elet _ | Eperiod _ | Eblock _ | Epresent _
    -> assert false
    
let rec equation return ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(p, e) ->
      let return, e = expression return e in
      { eq with eq_desc = EQeq(p, e ) }, return
  | EQinit(x, e) ->
     let return, e = expression return e in
     { eq with eq_desc = EQinit(x, e) }, return
  | EQreset(eq_list, e) ->
      let eq_list, return = Misc.map_fold equation return eq_list in
      let return, e = expression return e in
      { eq with eq_desc= EQreset(eq_list, e) }, return
  | EQmatch(total, e, p_h_list) ->
      let p_h_list, return =
        Misc.map_fold
          (fun return ({ m_body = b } as h) ->
             let return, b = block return b in
             { h with m_body = b }, return)
          return p_h_list in
      let e, return = expression return e in
      { eq with eq_desc = EQmatch(total, e, p_h_list) }, return
  | EQnext _ | EQblock _ | EQemit _ | EQautomaton _
  | EQpresent _ | EQder _ | EQpluseq _
  | EQand _| EQbefore _| EQforall _-> assert false

and block return ({ b_body = eq_list; b_env = b_env } as b) =
  let eq_list, return = Misc.map_fold equation return eq_list in
  { b with b_body = eq_list }, return

let local return ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, return = Misc.map_fold equation return eq_list in
  { l with l_eq = eq_list }, return

(* translate a top level expression *)
let let_expression return ({ e_desc = desc } as e) =
  match desc with
  | Elet(l, e) ->
      let l, return = local return l in
      let e, return = expression return e in
      { e with e_desc = Elet(l, e) }, return
  | _ -> expression return e

let implementation return impl =
  match impl.desc with
  | Eopen _ | Etypedecl _ | Econstdecl _ -> impl, return
  | Efundecl(n, ({ f_body = e } as body)) ->
      let e, return = expression return e in
      { impl with desc = Efundecl(n, { body with f_body = e }) }, return
               
let implementation_list impl_list =
  let impl_list, return = Misc.map_fold implementation empty impl_list in
  impl_list
 
