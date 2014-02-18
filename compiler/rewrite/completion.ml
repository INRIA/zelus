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
(* complete partial definitions with [next x = x] or [x = last(x)] and *)
(* identify assignments to shared variables. At the end, equations *)
(* on structured patterns like [pat = e] are such that no variable in [pat] *)
(* is shared. A equation on a shared variable is of the form [x = e] *)
open Location
open Ident
open Zelus
open Deftypes

let emake desc = 
  { e_desc = desc; e_loc = no_location; e_typ = Deftypes.no_typ }
let eqmake desc = 
  { eq_desc = desc; eq_loc = no_location }
let var n = 
  { e_desc = Elocal(n); e_loc = no_location; e_typ = Deftypes.no_typ }
let varpat n = 
  { p_desc = Evarpat(n); p_loc = no_location; p_typ = Deftypes.no_typ }
let wildpat () =
  { p_desc = Ewildpat; p_loc = no_location; p_typ = Deftypes.no_typ }

(* adds an equation [next x = x] or [x = last(x)] for every partially defined *)
(* variable in a control structure. *)
(* [defined_names] is the set of globally defined names in the control structure *)
(* [w] is the set of names written in the current handler *)
(* A variable [x] is partially defined if *)
(* [x in last_or_next(defined_names) \ w] *)
(* where [x in last_or_next(defined_names)] if [x] is a last or next variable *)
let complete_with_last_or_next env defined_names w eq_list =
  let last n = emake (Elast(n)) in
  let local n = emake (Elocal(n)) in
  (* add an equation [n = last n] or [next n = n] *)
  let equation n (eq_list, new_names) =
    let { Deftypes.t_sort = sort } = 
      try Env.find n env with Not_found -> assert false in
    let ok = S.mem n w in
    match sort with
      | Deftypes.Mem { Deftypes.t_is_set = true } when not ok ->
	  (* add an equation [n = last n] *)
	  (eqmake (EQeq(varpat n, last n))) :: eq_list, S.add n new_names
      | Deftypes.Mem { Deftypes.t_next_is_set = true } when not ok ->
	  (* add an equation [next n = n] *)
	  (eqmake (EQnext(varpat n, local n, None))) :: eq_list, S.add n new_names
      | _ -> eq_list, new_names in
  S.fold equation defined_names (eq_list, S.empty)

(* makes a list of copies [x = x_copy] or [next x = x_copy] *)
(* and extends the local environment with definitions for the [x_copy] *)
let add_copies env n_list n_env eq_list copies =
  (* is-it a next? *)
  let is_a_next x env =
    let { t_sort = sort } = try Env.find x env with Not_found -> assert false in
    match sort with
      | Mem { t_next_is_set = true } -> true
      | _ -> false in
  (* makes a value for [x_copy] *)
  let value entry = { entry with t_sort = Val } in
  let n_copy_list =
    List.fold_left (fun acc (x, x_copy) -> x_copy :: acc) n_list copies in
  let n_env =
    List.fold_left 
      (fun acc (x, x_copy) -> Env.add x_copy (value (Env.find x env)) acc)
      n_env copies in
  let eq_list =
    List.fold_left
      (fun acc (x, x_copy) ->
        (eqmake 
	   (if is_a_next x env then EQnext(varpat x, var x_copy, None)
	    else EQeq(varpat x, var x_copy))) :: acc) eq_list copies in
  n_copy_list, eq_list, n_env

(* [last p] returns an expression equal to [p] with every variable [x] from [p] *)
(* replaced by [last x] *)
let rec last { p_desc = desc; p_typ = ty; p_loc = loc } =
  let desc = match desc with
    | Econstpat(c) -> Econst(c)
    | Econstr0pat(c) -> Econstr0(c)
    | Etuplepat(p_list) -> Etuple(List.map last p_list)
    | Evarpat(n) -> Elast(n)
    | Erecordpat(label_pat_list) ->
        Erecord(List.map (fun (label, p) -> (label, last p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraint(last p, ty)
    | Ealiaspat _ | Eorpat _ | Ewildpat -> assert false in
  { e_desc = desc; e_typ = ty; e_loc = loc }

(* Make a defaut block with equations of the form [x = last x] *)
(* when a pattern matching is not exhaustive *)
let default_handler env defnames =
  let eq_list, new_names = 
    complete_with_last_or_next env defnames S.empty [] in
  { m_pat = wildpat ();
    m_body = { b_vars = []; b_locals = []; b_body = eq_list; 
               b_write = { Total.empty with dv = new_names }; 
	       b_loc = no_location; b_env = Env.empty };
    m_env = Env.empty;
    m_reset = false }

(* makes a copy of a pattern if it contains shared variables *)
(* introduce auxilary equations [x = x_copy] in [copies] *)
let rec pattern shared copies pat =
  match pat.p_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> pat, copies
    | Etuplepat(p_list) ->
        let p_list, copies =
          List.fold_right 
            (fun p (p_list, copies) -> 
              let p, copies = pattern shared copies p in
              p :: p_list, copies) p_list ([], copies) in
        { pat with p_desc = Etuplepat(p_list) }, copies
    | Evarpat(n) -> 
        if S.mem n shared then
          let ncopy = Ident.fresh "copy" in
          { pat with p_desc = Evarpat(ncopy) }, (n, ncopy) :: copies
        else pat, copies
    | Erecordpat(label_pat_list) ->
        let label_pat_list, copies =
          List.fold_right 
            (fun (label, p) (label_p_list, copies) -> 
              let p, env = pattern shared copies p in
              (label, p) :: label_p_list, copies) label_pat_list ([], copies) in
        { pat with p_desc = Erecordpat(label_pat_list) }, copies
    | Etypeconstraintpat(p, ty) ->
        let p, env = pattern shared copies p in
        { pat with p_desc = Etypeconstraintpat(p, ty) }, copies
    | Ealiaspat(p, n) ->
        let p, env = pattern shared copies p in
        let n, env = 
          if S.mem n shared then
            let ncopy = Ident.fresh "copy" in
            ncopy, (n, ncopy) :: copies
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

and equation shared env copies eq =
  match eq.eq_desc with
    | EQeq({ p_desc = Evarpat(n) } as pat, e) when S.mem n shared ->
        (* do nothing if [n] is shared *)
        { eq with eq_desc = EQeq(pat, exp e) }, copies
    | EQeq(pat, e) ->
        (* if some variable from [pat] are shared, [pat] is renamed into [pat'] *)
        (* and auxiliary equations [x1 = x_copy1 and ... and xn = x_copyn] *)
        (* are added *)
        let pat, copies = pattern shared copies pat in
        { eq with eq_desc = EQeq(pat, exp e) }, copies
    | EQder(n, e, None, []) ->
        let e = exp e in
        { eq with eq_desc = EQder(n, e, None, []) }, copies
    | EQinit(pat, e0, e_opt) ->
        let e0 = exp e0 in
        { eq with eq_desc = EQinit(pat, e0, Misc.optional_map exp e_opt) }, copies
    | EQnext({ p_desc = Evarpat(n) } as pat, e, None) when S.mem n shared -> 
        (* do nothing if [n] is shared *)
        let e = exp e in
        { eq with eq_desc = EQnext(pat, e, None) }, copies
    | EQnext(pat, e, None) ->
        (* if some variable from [pat] are shared, [pat] is renamed into [pat'] *)
        (* and auxiliary equations *)
        (* [next x1 = x_copy1 and ... and next xn = x_copyn ] are added *)
        let pat, copies = pattern shared copies pat in
        let e = exp e in
        { eq with eq_desc = EQeq(pat, e) }, copies
    | EQnext(pat, e, Some(e0)) ->
        (* if a initial value is given, then no variable from [pat] is shared *)
        { eq with eq_desc = EQnext(pat, exp e, Some(exp e0)) }, copies
    | EQmatch(total, e, p_h_list) ->
        (* first compute the set of names modified *)
        (* by at least one branch *)
        let defnames =
          List.fold_left
            (fun acc { m_body = { b_write = { dv = w } }} -> S.union acc w)
            S.empty p_h_list in
        let p_h_list =
          List.map 
            (fun ({ m_body = b } as handler) -> 
              { handler with m_body = block env defnames b }) p_h_list in
        (* if the pattern is not exhaustive, add an extra handler *)
        (* _ -> do x1 = last x1 / next x1 = x1 and ... done *)
        let p_h_list = 
          if !total then p_h_list
          else p_h_list @ [default_handler env defnames] in 
        { eq with eq_desc = EQmatch(ref true, exp e, p_h_list) }, copies
    | EQreset({ b_write = { dv = w } } as b, e) ->
        { eq with eq_desc = EQreset(block env w b, exp e) }, copies
    | EQemit _ | EQautomaton _ | EQpresent _ | EQder _ -> assert false

and equation_list shared env eq_list = 
  let equationrec (eq_list, copies) eq =
    let eq, copies = equation shared env copies eq in
    eq :: eq_list, copies in
  List.fold_left equationrec ([], []) eq_list
 
and local ({ l_eq = eq_list; l_env = env } as l) =
  let eq_list, _ = equation_list S.empty env eq_list in
  { l with l_eq = eq_list }
    
(* [env] is the current environment to track last and next variables in it. *)
(* [defnames] is the set of globally write variables. A new equation *)
(* [x = last x] or [next x = x] is added for every variable [x] such that *)
(* [x in defnames] and [x in last_or_next(env)] and [x not in b.b_write] *)
and block 
    env defnames 
  ({b_vars = n_list; b_body = eq_list; b_write = ({ dv = w } as defname); 
    b_env = n_env} as b) =
  let env = Env.append n_env env in
  let eq_list, copies = equation_list w env eq_list in
  let n_list, eq_list, n_env = add_copies env n_list n_env eq_list copies in
  let eq_list, new_names = 
    complete_with_last_or_next env defnames w eq_list in
  { b with b_vars = n_list; b_body = eq_list; 
    b_write = { defname with dv = S.union new_names w };
    b_env = n_env }

let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
