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
(* dead-code removal. applied on normalized and scheduled equations *)

open Misc
open Ident
open Vars
open Zelus
open Deftypes

(** Dead-code removal. First build a table [yn -> {x1,...,xk}] wich associate *)
(** the list of read variables used to produce yn *)
(** then recursively mark all useful variable according to read-in dependences *)
(** finally, only keep equations and name defs. for useful variables *)
(** the optimization is not very agressive, e.g., stateful functions are still *)
(** not removed *)
type table = cont Env.t
and cont = 
    { mutable c_vars: S.t; (* set of variables *)
      mutable c_unsafe: bool; (* the right hand-side of the equation is unsafe *)
      mutable c_stateful: bool; (* the right hand-side is stateful *)
      mutable c_necessary: bool; (* is-it a useful variable? *)
      mutable c_visited: bool; (* true when the node has been visited *)
    }

(** Empty block *)
let is_empty_block { b_locals = l; b_body = eq_list } = (l = []) && (eq_list = [])

(** Useful function. For debugging purpose. *)
let print f v =
  Format.eprintf "Useful variables (%s): %a@." f 
    (fun ff v -> Pp_tools.print_list_r Printer.name "" "," "" ff v) 
    (S.elements v)

(** make a new table where every entry depend also on variables in [x1,...,xk] *)
let extend table r =
  Env.map 
    (fun ( { c_vars = l } as cont) -> { cont with c_vars = S.union l r }) table

(** extends only for stateful/unsafe operations (reset construct) *)
let extend_stateful table r =
  Env.map 
    (fun ( { c_vars = l; c_unsafe = s; c_stateful = st } as cont) -> 
      if s || st then { cont with c_vars = S.union l r } else cont) table

(** Add an entry [x, cont] to an existing table. If x already exists *)
(** extends its definition. Otherwise, add the new entry *)
let add x ({ c_vars = l1; c_necessary = n1; c_unsafe = uns1; 
             c_stateful = st1; c_visited = v1 } as cont) table =
  try
    let ({ c_vars = l2; c_necessary = n2; c_unsafe = uns2; 
             c_stateful = st2; c_visited = v2 } as cont) = 
      Env.find x table in
    cont.c_vars <- S.union l1 l2;
    cont.c_unsafe <- uns1 || uns2;
    cont.c_stateful <- st1 || st2;
    cont.c_necessary <- n1 || n2;
    cont.c_visited <- v1 || v2;
    table
  with 
    | Not_found -> Env.add x cont table

(** Fusion of two tables *)
let merge table1 table2 = Env.fold add table2 table1
  
(** An expresssion is unsafe if it contains an unsafe operation. *)
let rec unsafe { e_desc = desc } =
  match desc with
    | Eapp(Eop(f), _) when not (Types.is_a_safe_function f) -> true
    | Etuple(e_list) | Eapp(_, e_list) -> List.exists unsafe e_list
    | Erecord_access(e, _) | Etypeconstraint(e, _) -> unsafe e
    | Erecord(f_e_list) ->
        List.exists (fun (_, e) -> unsafe e) f_e_list
    | Eseq(e1, e2) -> (unsafe e1) || (unsafe e2)
    | Elocal _ | Elast _ | Econst _ | Econstr0 _ | Eglobal _ | Eperiod _ -> false
    | Elet _ -> true
    | Epresent _ | Ematch _ -> assert false

(** An expression is stateful when it is an stateful application *)
(** or the use of a stateful synchronous primitive *)
let stateful { e_desc = desc } =
  match desc with
    | Eapp((Efby | Eunarypre | Eminusgreater), _) -> true
    | Eapp(Eop(f), _) when Types.is_a_node f -> true
    | _ -> false

(** Build a new pattern by removing all useless variables. They are *)
(** replaced by a wildcard *)
let rec pattern v ({ p_desc = desc } as p) =
  match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> p
    | Evarpat(n) -> if S.mem n v then p else { p with p_desc = Ewildpat }
    | Etuplepat(p_list) ->
        let p_list = List.map (pattern v) p_list in
        if List.for_all (fun { p_desc = desc } -> desc = Ewildpat) p_list
        then { p with p_desc = Ewildpat } else { p with p_desc = Etuplepat(p_list) }
    | Ealiaspat(p1, n) ->
        let ({ p_desc = desc } as p1) = pattern v p1 in
        if S.mem n v then { p with p_desc = Ealiaspat(p1, n) } else p1
    | Eorpat(p1, p2) ->
        let ({ p_desc = desc1 } as p1) = pattern v p1 in
        let ({ p_desc = desc2 } as p2) = pattern v p2 in
        if desc1 = Ewildpat then p2
        else if desc2 = Ewildpat then p1
        else { p with p_desc = Eorpat(p1, p2) }
    | Erecordpat(l_p_list) ->
        let l_p_list = List.map (fun (l, p) -> (l, pattern v p)) l_p_list in
        if List.for_all (fun (_, { p_desc = desc}) -> desc = Ewildpat) l_p_list
        then { p with p_desc = Ewildpat } 
        else { p with p_desc = Erecordpat(l_p_list) }
    | Etypeconstraintpat(p1, ty) ->
        let ({ p_desc = desc1 } as p1) = pattern v p1 in
        if desc1 = Ewildpat then { p with p_desc = Ewildpat }
        else { p with p_desc = Etypeconstraintpat(p1, ty) }

(** Build the association table [yk -> { x1,..., xn}] *)     
let rec build_equation table { eq_desc = desc } =
  match desc with
    | EQeq(p, e) | EQinit(p, e, None) | EQnext(p, e, None) ->
        (* is-it an unsafe or stateful expression? *)
        let uns = unsafe e in
        let st = stateful e in
        (* for every [x in w], add the link [x -> r] to table *)
        let w = fv_pat S.empty p in
        let w =
          if S.is_empty w && uns
          then S.singleton (Ident.fresh "dummy") else w in
        let r = fv S.empty S.empty e in
        S.fold 
          (fun x acc -> 
            Env.add x { c_vars = r; c_necessary = false; c_unsafe = uns; 
                        c_stateful = st; c_visited = false } 
            acc) w table          
    | EQmatch(_, e, m_h_list) ->
        let r = fv S.empty S.empty e in
        let table_list = List.map (fun { m_body = b } -> build_block b) m_h_list in
        let table_b = List.fold_left merge Env.empty table_list in
        merge table (extend table_b r)
    | EQreset(b, e) ->
        let r = fv S.empty S.empty e in
        let table_b = build_block b in
        let table_b = extend_stateful table_b r in
        merge table table_b
    | EQinit _ | EQnext _ | EQder _ | EQautomaton _ 
    | EQpresent _ | EQemit _ -> assert false

and build_block { b_body = eq_list } = build_equation_list Env.empty eq_list
  
and build_local table { l_eq = eq_list } =
  build_equation_list table eq_list
  
and build_equation_list table eq_list = List.fold_left build_equation table eq_list

(** Visit the table: recursively mark all necessary names *)
(** returns the set of useful read and write variables *)
let visit v table =
  let read = ref S.empty in
  let write = ref S.empty in
  (* recursively mark visited nodes which are necessary *)
  let rec visit x =
    try
      let ({ c_vars = l; c_visited = v } as entry) = 
        Env.find x table in
      entry.c_necessary <- true;
      write := S.add x !write;
      if not v then
        begin
          entry.c_visited <- true;
          S.iter visit l
        end
    with
        Not_found -> 
          (* otherwise, [x] is a useful read variable *)
          read := S.add x !read in
  (* visit roots. Only necessary/unsafe nodes are considered *)
  let rec root x 
      ({ c_vars = l; c_necessary = n; c_unsafe = uns; c_visited = v } as entry) =
    if (not v) && (n || uns) then
      begin
        entry.c_visited <- true;
        write := S.add x !write;
      S.iter visit l
      end in
  (* recursively mark useful nodes *)
  S.iter visit v;
  Env.iter root table;
  (* return the set of useful variables *)
  !write, !read

(** Remove useless equations. [v] is the set of useful variables *)
(* [st] is true if the equation is stateful *)
let rec remove_equation v (eq_list, st) ({ eq_desc = desc } as eq) =
  match desc with
    | EQeq(p, e) ->
        let uns_e = unsafe e in
        let st_e = stateful e in
        let w = fv_pat S.empty p in
        (* keep the equation if some variables from [w] are useful *)
        if uns_e || S.exists (fun x -> S.mem x v) w 
        then { eq with eq_desc = EQeq(pattern v p, e) } :: eq_list, st_e || st
        else eq_list, st
    | EQmatch(total, e, m_h_list) ->
        let m_h_list, st = 
          List.fold_right 
            (fun ({ m_body = b } as m_h) (m_h_list, st) -> 
              let b, st = remove_block v st b in
              { m_h with m_body = b } :: m_h_list, st)
            m_h_list ([], st) in
        if List.for_all (fun { m_body = b} -> is_empty_block b) m_h_list
        then eq_list, st
        else { eq with eq_desc = EQmatch(total, e, m_h_list) } :: eq_list, st
    | EQreset(b, e) ->
        let b, st_b = remove_block v st b in   
        if is_empty_block b then eq_list, st
        else if st_b
        then { eq with eq_desc = EQreset(b, e) } :: eq_list, true
        else { eq with eq_desc = 
                EQreset(b, { e with e_desc = Econst(Ebool(false)) }) } :: eq_list, st
    | EQinit _ | EQnext _ | EQder _ | EQautomaton _ 
    | EQpresent _ | EQemit _ -> assert false

and remove_equation_list v st eq_list = 
  let eq_list, st = List.fold_left (remove_equation v) ([], st) eq_list in
  List.rev eq_list, st

and remove_block v st 
    ({ b_vars = n_list; b_body = eq_list; 
       b_write = ({ dv = w } as defnames); b_env = n_env } as b) =
  let eq_list, st = remove_equation_list v st eq_list in
  let n_list = List.filter (fun n -> S.mem n v) n_list in
  let n_env = remove_env v n_env in
  let w = S.filter (fun x -> S.mem x v) w in
  { b with b_vars = n_list; b_body = eq_list; 
    b_write = { defnames with dv = w }; b_env = n_env }, st

and remove_local v ({ l_eq = eq_list; l_env = l_env } as l) (l_list, st) =
  let eq_list, st = remove_equation_list v st eq_list in
  let l_env = remove_env v l_env in
  if eq_list = [] then l_list, st
  else { l with l_eq = eq_list; l_env = l_env } :: l_list, st

(** Only keep an entry for [x] in the type environment [l_env] *)
(** when [x in v] *)
and remove_env v l_env = Env.filter (fun x entry -> S.mem x v) l_env

(** the main entry for expressions. Warning: [e] must be in normal form *)
let exp e =
  (* simplifies [e] and returns the set of useful variables *)
  let rec exprec ({ e_desc = desc } as e) =
    match desc with
      | Elet(l, e1) ->
          let e1, read = exprec e1 in
          let table = build_local Env.empty l in
          let write, read = visit read table in
          let l, _ = remove_local write l ([], false) in
          if l = [] then e1, read 
          else { e with e_desc = Elet(List.hd l, e1) }, read
      | _ -> let read = fv S.empty S.empty e in
             e, read in
  let e, _ = exprec e in
  e
  
let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
