(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* complete partial definitions with [next x = x], [x = last(x)] and *)
(* [der x = 0.0]. *)
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
  { eq_desc = desc; eq_loc = no_location; eq_before = S.empty; eq_after = S.empty }
let var n = 
  { e_desc = Elocal(n); e_loc = no_location; e_typ = Deftypes.no_typ }
let varpat n = 
  { p_desc = Evarpat(n); p_loc = no_location; p_typ = Deftypes.no_typ }
let wildpat () =
  { p_desc = Ewildpat; p_loc = no_location; p_typ = Deftypes.no_typ }
let zero =
  { e_desc = Econst(Efloat(0.0)); 
    e_loc = no_location; e_typ = Initial.typ_float }

(* adds an equation [next x = x] or [x = last(x)] or [der x = 0.0] *)
(* for every partially defined variable in a control structure. *)
(* [defined_names] is the set of globally defined names in the control *)
(* structure *)
(* [names = { der = der; dv = dv }] defines names written in the *)
(* current handler *)
(* A variable [x] is partially defined if *)
(* [x in defined_names \ names] *)
let complete_with_last_next_der env defined_names names eq_list =
  let last n = emake (Elast(n)) in
  let local n = emake (Elocal(n)) in
  (* add an equation [der n = 0.0] if no equation [n = ...] is present *)
  let der n (eq_list, acc) =
    if (S.mem n names.der) || (S.mem n names.dv) then eq_list, acc
    else (eqmake (EQder(n, zero, None, []))) :: eq_list, S.add n acc in
  (* add an equation [n = last n] or [next n = n] *)
  let last_of_next n (eq_list, acc) =
    let { Deftypes.t_sort = sort } = 
      try Env.find n env with Not_found -> 
	Misc.internal_error "Unbound variable" Printer.name n in
    let already = S.mem n names.dv in
    match sort with
      | Deftypes.Mem { Deftypes.t_is_set = true } when not already ->
	  (* add an equation [n = last n] *)
	  (eqmake (EQeq(varpat n, last n))) :: eq_list, S.add n acc
      | Deftypes.Mem { Deftypes.t_next_is_set = true } when not already ->
	  (* add an equation [next n = n] *)
	  (eqmake (EQnext(n, local n, None))) :: eq_list, S.add n acc
      | _ -> eq_list, acc in
  let eq_list, der = S.fold der defined_names.der (eq_list, names.der) in
  let eq_list, dv = S.fold last_of_next defined_names.dv (eq_list, names.dv) in
  eq_list, { names with dv = dv; der = der }

(* makes a list of copies [x = x_copy] or [next x = x_copy] *)
(* and extends the local environment with definitions for the [x_copy] *)
let add_copies env n_list n_env eq_list copies =
  (* is-it a next? *)
  let is_a_next x env =
    let { t_sort = sort } = 
      try Env.find x env 
      with Not_found -> Misc.internal_error "Unbound variable" Printer.name x in
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
	   (if is_a_next x env then EQnext(x, var x_copy, None)
	    else EQeq(varpat x, var x_copy))) :: acc) eq_list copies in
  n_copy_list, eq_list, n_env

(* Make a defaut block with equations of the form [x = last x] *)
(* or [next x = x] and possibly [der x = 0.0] *)
(* when a pattern matching is not exhaustive *)
let default_handler env defnames =
  let eq_list, new_names = 
    complete_with_last_next_der env defnames Total.empty [] in
  { m_pat = wildpat ();
    m_body = { b_vars = []; b_locals = []; b_body = eq_list; 
               b_write = new_names;
	       b_loc = no_location; b_env = Env.empty };
    m_env = Env.empty;
    m_reset = false; m_zero = false }

(* makes a copy of a pattern if it contains shared variables *)
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
          { pat with p_desc = Evarpat(ncopy) }, (n, ncopy) :: copies
        else pat, copies
    | Erecordpat(label_pat_list) ->
        let label_pat_list, copies =
          List.fold_right 
            (fun (label, p) (label_p_list, copies) -> 
              let p, env = pattern dv copies p in
              (label, p) :: label_p_list, copies) label_pat_list ([], copies) in
        { pat with p_desc = Erecordpat(label_pat_list) }, copies
    | Etypeconstraintpat(p, ty) ->
        let p, env = pattern dv copies p in
        { pat with p_desc = Etypeconstraintpat(p, ty) }, copies
    | Ealiaspat(p, n) ->
        let p, env = pattern dv copies p in
        let n, env = 
          if S.mem n dv then
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

(* [dv] is the set of names possibly written in [eq] which are visible *)
(* outside of the block *)
and equation dv env copies eq =
  match eq.eq_desc with
    | EQeq({ p_desc = Evarpat(n) } as pat, e) ->
       { eq with eq_desc = EQeq(pat, exp e) }, copies
    | EQeq(pat, e) ->
       (* if some variable from [pat] are shared, [pat] is renamed into [pat'] *)
       (* and auxiliary equations [x1 = x_copy1 and ... and xn = x_copyn] *)
       (* are added *)
       let pat, copies = pattern dv copies pat in
       { eq with eq_desc = EQeq(pat, exp e) }, copies
    | EQset _ -> eq, copies
    | EQder(n, e, None, []) ->
       { eq with eq_desc = EQder(n, exp e, None, []) }, copies
    | EQinit(n, e0) ->
       { eq with eq_desc = EQinit(n, exp e0) }, copies
    | EQnext(n, e, e_opt) ->
       { eq with eq_desc = EQnext(n, exp e, Misc.optional_map exp e_opt) }, copies
    | EQmatch(total, e, p_h_list) ->
        (* first compute the set of names modified *)
        (* by at least one branch *)
        let defnames =
          List.fold_left 
	    (fun acc { m_body = { b_write = w } } -> Total.union acc w)
	    Total.empty p_h_list in
        let p_h_list =
          List.map 
            (fun ({ m_body = b } as handler) -> 
              { handler with m_body = block env defnames b }) p_h_list in
        (* if the pattern is not exhaustive, add an extra handler *)
        (* _ -> do x1 = last x1 / next x1 = x1 / der x1 = 0.0 ... done *)
        let p_h_list = 
          if !total then p_h_list
          else p_h_list @ [default_handler env defnames] in 
        { eq with eq_desc = EQmatch(ref true, exp e, p_h_list) }, copies
    | EQreset(res_eq_list, e) ->
        let res_eq_list, copies = equation_list dv env copies res_eq_list in
	{ eq with eq_desc = EQreset(res_eq_list, exp e) }, copies
    | EQemit _ | EQautomaton _ | EQpresent _ | EQder _ | EQblock _ -> assert false

(* [dv] defines names modified by [eq_list] but visible outside of the block *)
and equation_list dv env copies eq_list = 
  let equationrec (eq_list, copies) eq =
    let eq, copies = equation dv env copies eq in
    eq :: eq_list, copies in
  List.fold_left equationrec ([], copies) eq_list
 
and local ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, copies = equation_list S.empty l_env [] eq_list in
  let _, eq_list, l_env = add_copies l_env [] l_env eq_list copies in
  { l with l_eq = eq_list; l_env = l_env }
    
(* [env] is the current environment to track last and next variables in it. *)
(* [defnames] is the set of globally write variables. A new equation *)
(* [x = last x] or [next x = x] is added for every variable [x] such that *)
(* [x in defnames] and [x in last_or_next(env)] and [x not in b.b_write] *)
and block 
      env defnames 
      ({ b_vars = n_list; b_body = eq_list; b_write = ({ dv = dv } as names); 
	b_env = n_env } as b) =
  let env = Env.append n_env env in
  let eq_list, copies = equation_list dv env [] eq_list in
  let n_list, eq_list, n_env = add_copies env n_list n_env eq_list copies in
  let eq_list, names = 
    complete_with_last_next_der env defnames names eq_list in
  { b with b_vars = n_list; b_body = eq_list; 
    b_write = names;
    b_env = n_env }

let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
