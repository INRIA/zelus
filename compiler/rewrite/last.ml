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
(* Compilation of lasts and nexts. this step comes after the elimination  *)
(* of all continuous-time features and normalization of resets.           *)
(* Once applied, expressions do not contain nested registers anymore         *)
(* that is                                                                   *)
(* [fby], [->], [last x], [next] have been eliminated.                       *)
(* The reset/every has been elimitated and pushed to function applications   *)
(* The transformation applies to programs in equational normal form          *)
(*                                                                           *)
(* Translation of registers: pre/fby/last/->                                 *)
(* introduce an initialization register in every control block               *)
(* [p = pre(e)] = [x' = e and x = pre(x')]                                   *)
(* [p = e1 fby e2] = [init = true fby false and x = if init then e1 else lx  *)
(*                    and lx = pre(e2)]                                      *) 
(* [p = e1 -> e2] = [init = true fby false and x = if init then e1 else e2]  *)
(*                                                                           *)
(* Translation of guards with initializations                                *)
(* [x = present z1 -> e1 | ... | zn -> en init e] =                          *)
(*     [x = present z1 -> e1 | ... | zn -> en else lx and lx = e fby x       *)
(* [x = e init e0] =                                                         *)
(*     [x = e0 -> e and lx = pre(x)                                          *)
(* [x = present z1 -> e1 | ... | zn -> en] =                                 *)
(*     [x = present z1 -> e1 | ... | zn -> en else last x]                   *)
(* every occurrence of last x is replaced by lx                              *)
(* [init p = e] is replaced by [lp = e1 fby p]                               *)

open Misc
open Location
open Deftypes
open Zelus
open Ident

(** Build basic operations *)
let make desc ty = 
  { e_desc = desc; e_loc = no_location; e_typ = ty }
let eqmake p e = { eq_desc = EQeq(p, e); eq_loc = no_location }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty }
let var n ty = make (Elocal(n)) ty
let varpat n ty = pmake (Evarpat(n)) ty
let efalse = make (Econst(Ebool(false))) Initial.typ_bool
let etrue = make (Econst(Ebool(true))) Initial.typ_bool
let boolpat n = pmake (Evarpat(n)) Initial.typ_bool
let boolvar n = make (Elocal(n)) Initial.typ_bool
let ifthenelse e1 e2 e3 =
  match e1.e_desc with
    | Econst(Ebool(true)) -> e2
    | _ -> { e2 with e_desc = Eapp(Eifthenelse, [e1; e2; e3]) }
let true_fby_false = make (Eapp(Efby, [etrue; efalse])) Initial.typ_bool
let pre_n n ty = make (Eapp(Eunarypre, [var n ty])) ty
let pre e = make (Eapp(Eunarypre, [e])) e.e_typ
let fby e1 e2 = make (Eapp(Efby, [e1; e2])) e1.e_typ
let or_op e1 e2 = 
  make (Eapp(Eop(Lident.Modname(Initial.pervasives_name "||")), [e1; e2])) 
    Initial.typ_bool

(** Build the substitution. *)
(* [build subst l_env = subst', l_env', eq_list'] *)
(* [subst'] is a new substitution that extends [subst] with fresh names *)
(* for last variables. [l_env'] extends [l_env] accordingly. *)
(* The substitution is used to replace [last x] by a fresh *)
(* name [lx] and [next x = e] by [nx = e] *)
(* add an equation [lx = pre(x)] when [last x] is used and *)
(* no equation [init x = e] is given. *)
(* add [x = lx] when [init x = e] is given but no definition for [x] nor *)
(* [next x] is given. All these equations are placed into [eq_list'] *)
let build subst l_env =
  let build n { t_sort = sort; t_typ = ty } (subst, l_env, eq_list) =
    match sort with
      | Mem { t_initialized = true; t_is_set = false; t_next_is_set = false } ->
          (* [init n = ...] but not equation [n = ...] is given *)
	  let ln = Ident.fresh "last" in
          Env.add n ln subst,
	  Env.add ln { t_sort = Val; t_typ = ty } l_env,
	  (eqmake (varpat n ty) (var ln ty)) :: eq_list
      | Mem { t_initialized = true; t_is_set = true } ->
	  (* [init n = ...] and an equation [n = ...] is given *)
	  let ln = Ident.fresh "last" in
          Env.add n ln subst,
	  Env.add ln { t_sort = Val; t_typ = ty } l_env,
	  eq_list 
      | Mem { t_initialized = true; t_next_is_set = true } ->
	  (* [init n = ...] and an equation [next n = ...] is given *)
	  let next_n = Ident.fresh "next_n" in
          Env.add n next_n subst,
	  Env.add next_n { t_sort = Val; t_typ = ty } l_env, eq_list 
      | Mem { t_initialized = false; t_last_is_used = true } ->
          (* no [init n = ...] but [last n] is used *)
	  let ln = Ident.fresh "last" in
          Env.add n ln subst,
	  Env.add ln { t_sort = Val; t_typ = ty } l_env,
	  (eqmake (varpat ln ty) (pre_n n ty)) :: eq_list	  
      | Val | ValDefault _ | Mem { t_initialized = false } -> 
	  subst, l_env, eq_list in
  Env.fold build l_env (subst, l_env, [])

(* modify the set of defnames of a block. A variable [x] defined by a [next x = ...] *)
(* equation is renamed into [nx]. Other are kept unchanged *)
let set_defnames env subst ({ dv = dv } as defnames) =
  let rename x =
    try 
      let nx = Env.find x subst in
      let { t_sort = sort } = Env.find x env in
      begin match sort with Mem { t_next_is_set = true } -> nx | _ -> x end
    with Not_found -> x in
  { defnames with dv = S.map rename dv }
  
(** Static expressions *)
let rec immediate { e_desc = desc } =
  match desc with
    | Econst _ | Econstr0 _ -> true
    | Etuple(e_list) -> List.for_all immediate e_list
    | Erecord(qual_e_list) -> 
        List.for_all (fun (_, e) -> immediate e) qual_e_list
    | Erecord_access(e, _) -> immediate e
    | _ -> false

(** Translation of a pattern. Rename all names *)
let rec pattern subst ({ p_desc = desc } as p) =
  let desc = match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> desc
    | Etuplepat(p_list) -> Etuplepat(List.map (pattern subst) p_list)
    | Evarpat(n) -> 
        begin try Evarpat(Env.find n subst) with Not_found -> desc end
    | Erecordpat(label_pat_list) ->
        Erecordpat(List.map 
                      (fun (label, p) -> (label, pattern subst p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraintpat(pattern subst p, ty)
    | Ealiaspat(p1, n) -> 
        let n = try Env.find n subst with Not_found -> n in
        Ealiaspat(pattern subst p1, n)
    | Eorpat(p1, p2) ->
        Eorpat(pattern subst p1, pattern subst p2) in
  { p with p_desc = desc }

(** Copy of a pattern. Rename all names *)
let rec copy env ({ p_desc = desc; p_typ = ty } as p) =
  let desc, env = match desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> desc, env
    | Etuplepat(p_list) -> 
        let p_list, env =
          List.fold_right 
            (fun p (p_list, env) -> let p, env = copy env p in p :: p_list, env) 
            p_list ([], env) in
        Etuplepat(p_list), env
    | Evarpat(n) -> 
        let n_copy = Ident.fresh "copy" in
        Evarpat(n_copy), Env.add n_copy { t_sort = Val; t_typ = ty } env
    | Erecordpat(label_pat_list) ->
        let label_pat_list, env =
          List.fold_right 
            (fun (l, p) (l_p_list, env) -> 
              let p, env = copy env p in (l, p) :: l_p_list, env) 
            label_pat_list ([], env) in
        Erecordpat(label_pat_list), env
    | Etypeconstraintpat(p, ty) -> 
        let p, env = copy env p in
        Etypeconstraintpat(p, ty), env
    | Ealiaspat _ | Eorpat _ -> assert false in
  { p with p_desc = desc }, env

(** left_right of two patterns. [left_right n m] returns *)
(** [n, m] when [next(n)], [m, n] otherwise. [left_right pat1 pat2] applies *)
(** this recursively *)
let rec left_right env ({ p_desc = desc1 } as p1) ({ p_desc = desc2 } as p2) = 
  let desc1, desc2 = match desc1, desc2 with
    | Ewildpat, _ | Econstpat _, _ | Econstr0pat _, _ -> desc1, desc2
    | Etuplepat(p_list1), Etuplepat(p_list2) ->
        let p_list12 = List.map2 (left_right env) p_list1 p_list2 in
	let p_list1, p_list2 = List.split p_list12 in
	Etuplepat(p_list1), Etuplepat(p_list2)
    | Evarpat(n), Evarpat(m) -> 
        let { t_sort = sort } = try Env.find n env with Not_found -> assert false in
	begin match sort with
	  | Mem { t_next_is_set = true } -> desc1, desc2 | _ -> desc2, desc1
	end
    | Erecordpat(label_pat_list1), Erecordpat(label_pat_list2) ->
        let label_pat_list12 =
	  List.map2 
	    (fun (label1, p1) (label2, p2) -> 
	      let p1, p2 = left_right env p1 p2 in
	      (label1, p1), (label2, p2))
	    label_pat_list1 label_pat_list2 in
	let label_pat_list1, label_pat_list2 = List.split label_pat_list12 in
	Erecordpat(label_pat_list1), Erecordpat(label_pat_list2)
    | Etypeconstraintpat(p1, ty1), Etypeconstraintpat(p2, ty2) -> 
        let p1, p2 = left_right env p1 p2 in
	Etypeconstraintpat(p1, ty1), Etypeconstraintpat(p2, ty2)
    | Ealiaspat(p1, n1), Ealiaspat(p2, n2) -> 
        let p1, p2 = left_right env p1 p2 in
	Ealiaspat(p1, n1), Ealiaspat(p2, n2)
    | Eorpat(p1, p2), Eorpat(p11, p22) ->
        let p1, p11 = left_right env p1 p11 in
	let p2, p22 = left_right env p2 p22 in
	Eorpat(p1, p2), Eorpat(p2, p22)
    | _ -> desc1, desc2 in
  { p1 with p_desc = desc1 }, { p2 with p_desc = desc2 }

(** Transform a state modification [(p1,...,pn) = (e01,...,e0n) fby (e1,...,en)] *)
(** into [p1 = e01 fby e1] and ... and [pn = e0n fby en] *)
let distribute_fby_state eq_list p e0 e =
  let rec map3 eq_list p_list e0_list e_list =
    match p_list, e0_list, e_list with
      | [], _, _ -> eq_list
      | p :: p_list, e0 :: e0_list, e :: e_list ->
          map3 (map eq_list p e0 e) p_list e0_list e_list
      | _ -> assert false
  and map eq_list p e0 e =
    match p.p_desc, e0.e_desc, e.e_desc with
      | Etuplepat(p_list), Etuple(e0_list), Etuple(e_list) ->
          map3 eq_list p_list e0_list e_list
      | _ -> 
          (eqmake p { e with e_desc = Eapp(Efby, [e0; e]) }) :: eq_list in
  map eq_list p e0 e

(** Transform a state modification [(p1,...,pn) = pre (e1,...,en)] *)
(** into [p1 = pre e1] and ... and [pn = pre en] *)
let distribute_pre_state eq_list p e =
  let rec map2 eq_list p_list e_list =
    match p_list, e_list with
      | [], _ -> eq_list
      | p :: p_list, e :: e_list ->
          map2 (map eq_list p e) p_list e_list
      | _ -> assert false
  and map eq_list p e =
    match p.p_desc, e.e_desc with
      | Etuplepat(p_list), Etuple(e_list) ->
          map2 eq_list p_list e_list
    | _ -> 
        (eqmake p { e with e_desc = Eapp(Eunarypre, [e]) }) :: eq_list in
  map eq_list p e

(** Translation a pattern into an expression *)
let rec exp_of_pat { p_desc = desc; p_loc = loc; p_typ = typ } =
  let desc = match desc with
    | Econstpat(i) -> Econst(i)
    | Econstr0pat(n) -> Econstr0(n)
    | Etuplepat(p_list) -> Etuple(List.map exp_of_pat p_list)
    | Evarpat(n) -> Elocal(n)
    | Erecordpat(label_pat_list) ->
        Erecord(List.map 
                   (fun (label, p) -> (label, exp_of_pat p)) label_pat_list)
    | Etypeconstraintpat(p, ty) -> Etypeconstraint(exp_of_pat p, ty)
    | Ewildpat | Ealiaspat _ | Eorpat _ -> assert false in
  { e_desc = desc; e_loc = loc; e_typ = typ }

(** The type for the initialization register *)
type init = 
    { value: exp;         (* its value *) 
      reset: bool;        (* is-it a reset? *)
      mutable used: bool; (* is-it used? *)
    }

let intro_init v = { used = false; reset = false; value = v }
let initial ({ value = e } as init) = init.used <- true; e
let used { used = used } = used
let reset { reset = reset } = reset
let add ({ value = e } as init) e0 = 
  init.used <- true; { init with reset = true; value = or_op e e0 }

(* Translate an initialization [init pat = e0] *)
let translate_init subst init env eq_list pat e0 =
  let subst_pat = pattern subst pat in
  (* if [next(pat)] then [left_pat = pat, right_pat = subst_pat] *)
  (* and [subst_pat, pat] otherwise *)
  let left_pat, right_pat = 
    left_right env pat subst_pat in
  let right_exp = exp_of_pat right_pat in
  if (immediate e0) && not (used init)
  then (* translate it into [x = e0 fby nx] if next(x) *)
       (* [lx = e0 fby x] otherwise *)
       distribute_fby_state eq_list left_pat e0 right_exp, env
  else 
       (* translate it into [px = pre(nx); x = if init then e0 else px] *)
       (* if next(x) *)
       (* [px = pre(x); lx = if init then e0 else px] otherwise *)
       let px, env = copy env left_pat in
       let eq_list = distribute_pre_state eq_list px right_exp in
       (eqmake left_pat (ifthenelse (initial init) e0 (exp_of_pat px))) :: 
	 eq_list,env
  
(** Translate an equation [next pat = e] into [n_pat = e] *)
let translate_next subst eq_list pat e =
  let n_pat = pattern subst pat in
  (eqmake n_pat e) :: eq_list

(** Candidate for compilation *)
let register op = 
  match op with 
    | Efby | Eunarypre | Eminusgreater | Eevery _ -> true 
    | Eop(f) when Types.is_a_node f -> true
    | _ -> false

(** Compile statefull functions. [subst] is used for replacing [last x] by *)
(** a fresh name; [env] is the current environment to be extended with new names *)
(** [eq_list] is the current list of equations *)
let apply subst init eq_list env op e_list e_result =
  match op, e_list with
    | Eunarypre, _ -> e_result, eq_list, env
    | Eminusgreater, [e1; e2] ->
        (* returns if initial(init) then e1 else e2 *)
        ifthenelse (initial init) e1 e2, eq_list, env
    | Efby, [v1; e2] when (immediate v1) && not (used init) ->
        (* we simply introduce a fresh name *)
        let y = Ident.fresh "copy" in
	fby v1 (var y e2.e_typ),
	(eqmake (varpat y e2.e_typ) e2) :: eq_list,
	Env.add y { t_sort = Val; t_typ = e2.e_typ } env
    | Efby, [e1; e2] ->
        (* introduce y = pre(e2) *)
        (* returns if initial(init) then e1 else y *)
        let y = Ident.fresh "pre" in
        ifthenelse (initial init) e1 (var y e2.e_typ),
        (eqmake (varpat y e2.e_typ) (pre e2)) :: eq_list, 
        Env.add y { t_sort = Val; t_typ = e2.e_typ } env
    | Eop(f), e_list ->
        (* [f] is a statefull function. The application is reset *)
        (* when init defines a reset *)
        let e_result = 
	  if reset init then 
	    { e_result with e_desc = Eapp(Eevery(f), (initial init) :: e_list) }
	  else { e_result with e_desc = Eapp(Eop(f), e_list) }
	in e_result, eq_list, env
    | Eevery(f), e :: e_list ->
        let e = 
	  if reset init then initial (add init e) else e in
	let e_result = 
	  { e_result with e_desc = Eapp(Eevery(f), e :: e_list) } in
	e_result, eq_list, env
    | _ -> assert false

(** Translation of expressions *)
(* [exp subst e = e'] returns a new expression [e']. [subst] is a *)
(* substitution used to replace last y by a fresh name. *)
let rec exp subst e = 
  match e.e_desc with
    | Econst _ | Econstr0 _ | Eglobal _ | Elocal _ -> e
    | Elast(n) ->
        begin try { e with e_desc = Elocal(Env.find n subst) } 
	  with Not_found -> e end
    | Etuple(e_list) ->
        { e with e_desc = Etuple(List.map (exp subst) e_list) }
    | Eapp(op, e_list) ->
        { e with e_desc = Eapp(op, List.map (exp subst) e_list) }
    | Erecord(label_e_list) ->
        { e with e_desc = 
            Erecord(List.map (fun (l, e) -> l, exp subst e) label_e_list) }
    | Erecord_access(e1, longname) ->
        { e with e_desc = Erecord_access(exp subst e1, longname) }
    | Etypeconstraint(e1, ty) ->
        { e with e_desc = Etypeconstraint(exp subst e1, ty) }
    | Elet(l, e_let) ->
        { e with e_desc = Elet(local subst l, exp subst e_let) }
    | Eseq(e1, e2) ->
        { e with e_desc = Eseq(exp subst e1, exp subst e2) }
    | Eperiod _ | Epresent _ | Ematch _ -> assert false

(** Equations *)
(* [subst] is a substitution to replace [last x] by a fresh name *)
(* and [next x = e] by an equation *)
(* [init] is the initialization register of the current block. *)
(* [env] is extended with fresh names for the translation of registers *)
and equation subst init (eq_list, env) ({ eq_desc = desc } as eq) =
  match desc with
    | EQeq(pat, ({ e_desc = Eapp(op, e_list) } as e_result)) when register op ->
        let e_list = List.map (exp subst) e_list in
        let e, eq_list, env = 
	  apply subst init eq_list env op e_list e_result in
        { eq with eq_desc = EQeq(pat, e) } :: eq_list, env
    | EQeq(pat, e) -> { eq with eq_desc = EQeq(pat, exp subst e) } :: eq_list, env
    | EQnext(pat, e, e0_opt) ->
        (* introduce an equation [n_pat = e]. If [e0_opt = Some(e0)] *)
        (* add [pat = e0 -> pre(n_pat)] *)
        let e = exp subst e in
	let e0_opt = Misc.optional_map (exp subst) e0_opt in
	let eq_list = translate_next subst eq_list pat e in
	let eq_list, env = 
	  match e0_opt with
	    | None -> eq_list, env
	    | Some(e0) -> translate_init subst init env eq_list pat e0 in
	eq_list, env
    | EQinit(pat, e0, e_opt) ->
        (* this is a shortcut for [lpat = e0 fby pat]) *)
        let e0 = exp subst e0 in
        let eq_list, env = translate_init subst init env eq_list pat e0 in
	let eq_list = 
	  match e_opt with 
	    | None -> eq_list 
	    | Some(e) -> { eq with eq_desc = EQeq(pat, exp subst e) } :: eq_list in
	eq_list, env
    | EQmatch(total, e, p_h_list) ->
        let e = exp subst e in
        let p_h_list = 
          List.map 
            (fun ({ m_body = b } as h) -> { h with m_body = block subst b }) 
            p_h_list
        in
        { eq with eq_desc = EQmatch(total, e, p_h_list) } :: eq_list, env
    | EQreset(b, e) ->
        reset init env eq_list subst (exp subst e) b
    | EQder _ | EQemit _ | EQautomaton _ 
    | EQpresent _ -> assert false

(* propagate a reset condition to a block *)
and reset init env eq_list subst e { b_body = body_eq_list; b_env = n_env } =
  let subst, n_env, new_eq_list = build subst n_env in
  let eq_list, n_env = 
    equation_list subst (add init e) n_env body_eq_list 
      (new_eq_list @ eq_list) in
  eq_list, Env.append n_env env
        
and equation_list subst init env eq_list acc = 
  List.fold_left (equation subst init) (acc, env) eq_list

and local subst ({ l_eq = eq_list; l_env = l_env } as l) =
  (* we add equations [lx1 = pre(x1),...,lxn = pre(xn)] *)
  (* for every non-initialized memory such as last(xi) is used *)
  (* Otherwise, at initialization points *)
  (* an equation [init pat = e] is translated either into *)
  (* [cur_pat = e -> pre(last_pat)] with [cur_pat = pat] and [last_pat = n_pat] *)
  (* if [past] is defined by a next; [cur_pat = l_pat] and [last_pat = pat] *)
  (* when [last pat] is used *)
  let subst, l_env, new_eq_list = build subst l_env in
  
  (* we introduce a fresh initialization register for every new block *)
  let i = Ident.fresh "init" in
  let init = intro_init (boolvar i) in
  let eq_list, l_env = equation_list subst init l_env eq_list new_eq_list in
  let eq_list, l_env =
    if used init then 
      (eqmake (boolpat i) true_fby_false) :: eq_list, 
      Env.add i { t_sort = Val; t_typ = Initial.typ_bool } l_env
    else eq_list, l_env in
  { l with l_eq = eq_list; l_env = l_env }

(** Blocks *)
and block subst 
    ({ b_body = eq_list; b_env = n_env; b_write = defnames } as b) =
  (* we introduce a fresh initialization register for every new block *)
  let i = Ident.fresh "init" in
  let init = intro_init (boolvar i) in
  (* add equations and new declarations for fresh names introduced to *)
  (* translate [last x] and [next x = ...] *)
  let subst, n_env, new_eq_list = build subst n_env in
  
  let eq_list, n_env = equation_list subst init n_env eq_list new_eq_list in
  let eq_list, n_env =
    if used init then
      (eqmake (boolpat i) true_fby_false) :: eq_list,
      Env.add i { t_sort = Val; t_typ = Initial.typ_bool } n_env
    else eq_list, n_env in
  let n_list = Env.fold (fun x _ acc -> x :: acc) n_env [] in
  let defnames = set_defnames n_env subst defnames in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env; b_write = defnames }
  
let implementation impl =
  match impl.desc with
      | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl(_, { f_kind = A }) -> impl
      | Efundecl(n, ({ f_body = e } as body)) ->
          { impl with desc = Efundecl(n, { body with f_body = exp Env.empty e }) }

let implementation_list impl_list = Misc.iter implementation impl_list
