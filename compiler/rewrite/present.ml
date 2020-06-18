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

(* removing present statements *)
open Misc
open Location
open Ident
open Lident
open Global
open Zelus
open Zaux
open Initial
open Types
open Deftypes

(* compilation of signal pattern matching                               *)
(* present                                                              *)
(*   | x1(p1) & ... & -> do ... done                                    *)
(*   | x2(p2) & x1(p3) & ...                                            *)
(*   end                                                                *)
(*                                                                      *)
(*   - rewrite the pattern matching such a signal name is assigned to   *)
(*   a column. Boolean conditions are put in an extra column.           *)
(*                                                                      *)
(*   present                                                            *)
(*   | x1(p1) & ... & cond1 -> do ... done                              *)
(*   | x1(p3) & ... & cond2 -> ...                                      *)
(*   end                                                                *)
(*                                                                      *)
(*   - then produce a regular pattern matching construct                *)
(*     every handler is marked to be activated on an event              *)
(*                                                                      *)
(*   match x1, ... cond1, ..., condn with                               *)
(*   | Present(p1), ..., true, ... -> (* zero = true *) ...             *)
(*   | Present(p3), ..., _,  true -> (* zero = true *) ...              *)
(*   end                                                                *)
(* the bit [zero] indicates that the branch corresponds to a *)
(* zero-crossing. It is set to [true] only when the context is continuous *)
(*                                                                      *)
(*                                                                      *)
(* a signal x is represented by a pair (bit, value)                     *)


(** representation of signals *)
(* a [signal] is a pair made of a value and a boolean *)
let emit e = e, etrue
let presentpat pat =
  { pat with p_desc = Etuplepat[pat; truepat];
             p_typ = tproduct [pat.p_typ; typ_bool] }

(* implementation of the presence test ? of a signal *)
let test e = Eapp(Zaux.prime_app,
                  Zaux.global_in_stdlib "snd"
                    (maketype [e.e_typ] Initial.typ_bool),
                  [e])
    
let eq_match total e l = 
  let block_do_done =
    { b_vars = []; b_locals = []; b_body = []; b_loc = no_location;
      b_env = Env.empty; 
      b_write = Deftypes.empty } in
  (* if [total = false] complete with an empty block [do done] *)
  let l = if total then l
    else l @ [{ m_pat = { Zaux.wildpat with p_typ = e.e_typ };
                m_body = block_do_done; m_env = Env.empty;
		m_reset = false; m_zero = false }] in
  eqmake (EQmatch(ref true, e, l))

(* build the environment for signals from a typing environment *)
(* every signal [x: t sig] is associated to a pair [xv, xp] of two fresh *)
(* names. [xv: t] and [xp: bool] *)
let build signals l_env =
  let make n ({ t_typ = ty; t_sort = sort } as tentry)
	   (signals, n_list, new_env) = 
    match Types.is_a_signal ty with
      | Some(ty) ->
	  let xv = Ident.fresh ((Ident.source n) ^ "v") in
	  let xp = Ident.fresh ((Ident.source n) ^ "p") in
	  let sort_v, sort_p =
	    match sort with
	    | Sstatic -> Sstatic, Sstatic
	    | Sval -> Sval, Sval
	    | Svar _
	    | Smem _ -> Deftypes.variable,
			Svar { v_combine = None;
			       v_default = Some(Cimmediate(Ebool(false))) } in
	  Env.add n (xv, xp, ty) signals,
	  (Zaux.vardec xv) :: (Zaux.vardec xp) :: n_list,
	  Env.add xv { t_typ = ty; t_sort = sort_v }
		  (Env.add xp { t_typ = typ_bool; t_sort = sort_p } new_env)
      | None ->
	signals, (Zaux.vardec_from_entry n tentry) :: n_list,
	Env.add n tentry new_env in
  Env.fold make l_env (signals, [], Env.empty)

(* equality between expressions. for efficiency purpose *)
(* we restrict to simple cases *)
let equal e1 e2 =
  match e1.e_desc, e2.e_desc with
    | Econst(i), Econst(j) when (i = j) -> true
    | Elocal(i), Elocal(j) when (i = j) -> true
    | Elast(i), Elast(j) when (i = j) -> true
    | _ -> false

(* the member function *)
let mem e exps = List.exists (equal e) exps

(* rename written variables [w] according to a substitution [signals] *)
(* the field [w.dr] is not concerned *)
let defnames signals ({ dv = dv; di = di } as w) =
  let defname n acc = 
    try let nv, np, _ = Env.find n signals in S.add nv (S.add np acc)
    with Not_found -> S.add n acc in
  { w with dv = S.fold defname dv S.empty; di = S.fold defname di S.empty }

(* separate signal testing from boolean condition in a signal pattern *)
let split spat =
  let rec split (se_list, pat_list, cond_list) spat =
    match spat.desc with
      | Econdand(sp1, sp2) | Econdor(sp1, sp2) ->
          split (split (se_list, pat_list, cond_list) sp2) sp1
      | Econdexp(e) ->
          se_list, pat_list, e :: cond_list
      | Econdon(sp1, e) ->
	  let se_list, pat_list, cond_list = 
	    split (se_list, pat_list, cond_list) sp1 in
	  se_list, pat_list, e :: cond_list
      | Econdpat(e, pat) ->
          e :: se_list, pat :: pat_list, cond_list in
  split ([], [], []) spat

let rec pattern signals p =
  match p.p_desc with
  | Ewildpat | Econstpat _ | Econstr0pat _ -> p
  | Etuplepat(p_list) -> 
      { p with p_desc = Etuplepat(List.map (pattern signals) p_list) }
  | Econstr1pat(c, p_list) -> 
      { p with p_desc = Econstr1pat(c, List.map (pattern signals) p_list) }
  | Evarpat(n) ->
      begin try 
          let nv, np, ty = Env.find n signals in
	  { p with p_desc = Etuplepat [varpat nv ty; varpat np typ_bool] }
        with 
        | Not_found -> p
      end
  | Ealiaspat(p1, n) ->
      { p with p_desc = Ealiaspat(pattern signals p1, n) }
  | Eorpat(p1, p2) ->
      { p with p_desc = Eorpat(pattern signals p1, pattern signals p2) }
  | Erecordpat(l_p_list) ->
      let l_p_list = 
        List.map (fun (l, p) -> (l, pattern signals p)) l_p_list in
      { p with p_desc = Erecordpat(l_p_list) }
  | Etypeconstraintpat(p1, ty) ->
      { p with p_desc = Etypeconstraintpat(pattern signals p1, ty) }
      
let rec exp signals ({ e_desc = desc } as e) =
  let desc = match desc with
    | Econst _ | Econstr0 _ | Eglobal _ -> desc
    | Elast(name) ->
       begin try 
           let nv, np, ty = Env.find name signals in
           Etuple [last nv ty; last np typ_bool]
       with 
       | Not_found -> desc
       end
    | Elocal(name)-> 
       begin try 
           let nv, np, ty = Env.find name signals in
           Etuple [var nv ty; var np typ_bool]
       with 
       | Not_found -> desc
       end
    | Etuple(e_list) -> Etuple(List.map (exp signals) e_list)
    | Econstr1(c, e_list) -> Econstr1(c, List.map (exp signals) e_list)
    | Eop(Etest, [e]) -> test (exp signals e)
    | Eop(op, e_list) ->
        Eop(op, List.map (exp signals) e_list)
    | Eapp(app, e, e_list) ->
        Eapp(app, exp signals e, List.map (exp signals) e_list)
    | Erecord(label_e_list) ->
        Erecord(List.map
	          (fun (label, e) -> (label, exp signals e)) label_e_list)
    | Erecord_access(e_record, longname) ->
       Erecord_access(exp signals e_record, longname)
    | Erecord_with(e_record, label_e_list) ->
       Erecord_with(exp signals e_record,
		    List.map
	              (fun (label, e) -> (label, exp signals e)) label_e_list)
    | Etypeconstraint(e, ty) -> Etypeconstraint(exp signals e, ty)
    | Eseq(e1, e2) -> Eseq(exp signals e1, exp signals e2)
    | Eperiod { p_phase = p1; p_period = p2 } ->
       Eperiod { p_phase = Misc.optional_map (exp signals) p1;
                 p_period = exp signals p2 }
    | Elet(l, e) -> 
        let signals, l = local signals l in Elet(l, exp signals e)
    | Eblock(b, e) ->
        let signals, b = block signals b in
        Eblock(b, exp signals e)
    | Epresent _ | Ematch _ -> assert false in
  { e with e_desc = desc }
  
and equation signals eq_list eq =
  match eq.eq_desc with
  | EQeq(pat, e) -> 
      { eq with eq_desc =
	          EQeq(pattern signals pat, exp signals e) } :: eq_list
  | EQpluseq(x, e) -> 
      { eq with eq_desc = EQpluseq(x, exp signals e) } :: eq_list
  | EQinit(x, e0) -> 
      { eq with eq_desc = EQinit(x, exp signals e0) } :: eq_list
  | EQnext(x, e, e0_opt) ->
      { eq with eq_desc =
	          EQnext(x, exp signals e, 
		  optional_map (exp signals) e0_opt) } :: eq_list
  | EQder(x, e, None, []) ->
      { eq with eq_desc = EQder(x, exp signals e, None, []) } :: eq_list
  | EQemit(name, e_opt) ->
      (* essentially translate to [(namev,namep) = e] *)
      let e = match e_opt with | None -> evoid | Some(e) -> exp signals e in
      let nv, np, ty = Env.find name signals in
      let ev, ep = emit e in
      { eq with eq_desc = EQeq(varpat nv ty, ev) } ::
      { eq with eq_desc = EQeq(varpat np typ_bool, ep) } :: eq_list
  | EQmatch(total, e, match_handler_list) ->
      { eq with eq_desc =
                  EQmatch(total, exp signals e, 
                          List.map (match_handler signals) match_handler_list) } 
      :: eq_list
  | EQpresent(present_handler_list, b_opt) ->
      present_handlers signals eq_list present_handler_list b_opt
  | EQreset(res_eq_list, e) ->
      let res_eq_list = equation_list signals res_eq_list in
      { eq with eq_desc = EQreset(res_eq_list, exp signals e) } :: eq_list
  | EQand(and_eq_list) ->
      { eq with eq_desc = EQand(equation_list signals and_eq_list) } :: eq_list
  | EQbefore(before_eq_list) ->
      { eq with eq_desc =
		  EQbefore(equation_list signals before_eq_list) } :: eq_list
  | EQblock(b) ->
      let _, b = block signals b in
      { eq with eq_desc = EQblock(b) } :: eq_list
  | EQforall ({ for_index = i_list; for_init = init_list;
		for_body = b_eq_list } as body) ->
      let index ({ desc = desc } as ind) =
	let desc = match desc with
          | Einput(x, e) -> Einput(x, exp signals e)
          | Eoutput _ -> desc
          | Eindex(x, e1, e2) ->  Eindex(x, exp signals e1, exp signals e2) in
        { ind with desc = desc } in
      let init ({ desc = desc } as ini) =
	let desc = match desc with
          | Einit_last(x, e) -> Einit_last(x, exp signals e) in
        { ini with desc = desc } in
      let _, b_eq_list = block signals b_eq_list in
      { eq with eq_desc =
		  EQforall
                      { body with for_index = List.map index i_list;
			          for_init = List.map init init_list;
			          for_body = b_eq_list } }
      :: eq_list
  | EQautomaton _ | EQder _ -> assert false
    
and equation_list signals eq_list =
  List.fold_left (equation signals) [] eq_list

and local signals ({ l_eq = eq_list; l_env = l_env } as l) =
  (* for every signal [s] declared in [env], we introduce *)
  (* a pair of names [sv, sp] for the value and presence *)
  let signals, _, l_env = build signals l_env in
  let eq_list = equation_list signals eq_list in
  signals, { l with l_eq = eq_list; l_env = l_env }

and locals signals l_list =
  match l_list with
  | [] -> signals, []
  | l :: l_list -> 
     let signals, l = local signals l in 
     let signals, l_list = locals signals l_list in
     signals, l :: l_list

and block signals 
    ({ b_vars = n_list; b_locals = l_list; 
       b_body = eq_list; b_env = b_env; b_write = w } as b) =
  (* for every signal [s] declared in [b_env], we introduce *)
  (* a pair of names [sv, sp] for the value and presence *)
  let signals, n_list, b_env = build signals b_env in
  let signals, l_list = locals signals l_list in
  let eq_list = equation_list signals eq_list in
  (* rename variables in [w] *)
  let w = defnames signals w in
  signals, { b with b_vars = n_list; b_locals = l_list; 
		    b_body = eq_list; b_write = w; b_env = b_env }

and match_handler signals ({ m_body = b } as handler) =
  let _, b = block signals b in { handler with m_body = b }

(* Translating a present statement *)
(* a present statement is translated into a pattern-matching statement *)
(* [is_cont = true] means that the present constructs run in a continuous context *)
and present_handlers signals eq_list handler_list b_opt =
  (* compute the set of expressions from a signal pattern matching *)
  (* expressions appearing more than once are shared *)
  let rec unique exps spat =
    match spat.desc with
      | Econdand(spat1, spat2) | Econdor(spat1, spat2) -> 
	  unique (unique exps spat1) spat2
      | Econdexp(e) | Econdpat(e, _) ->
          if mem e exps then exps
          else e :: exps
      | Econdon(spat1, e) ->
          unique (if mem e exps then exps else e :: exps) spat1 in

  let unique handler_list =
    List.fold_left
      (fun exps { p_cond = spat } -> unique exps spat) [] handler_list in

  (* normalize a signal pattern *)
  let rec norm spat acc =
    match spat.desc with
      | Econdor(spat1, spat2) -> norm spat1 (norm spat2 acc)
      | Econdpat _ | Econdexp _ | Econdand _ | Econdon _ -> spat :: acc in

  (* find the pattern associated to a signal in a signal pattern *)
  let pat spat se cont =
    let rec patrec spat =
      match spat.desc with
        | Econdand(spat1, spat2) ->
            begin try patrec spat1 with Not_found -> patrec spat2 end
        | Econdpat(e, pat) when (equal e se) || (e == se) -> presentpat pat
        | Econdexp(e) when (equal e se) || (e == se) -> truepat
        | Econdon(_, e) when (equal e se) || (e == se) -> truepat
	| Econdon(spat1, _) -> patrec spat1
	| _ -> raise Not_found in
    try
      (patrec spat) :: cont
    with
      Not_found ->
        { Zaux.wildpat with p_typ = se.e_typ } :: cont in

  (* build the pattern *)
  let pattern exps { p_cond = spat; p_body = b; p_env = h0 } =
    let pattern spat =
      let pat_list = List.fold_right (pat spat) exps [] in
      match pat_list with
	| [] -> assert false
	| [pat] -> pat
	| _ -> tuplepat(pat_list) in
    (* extract the list of simple signals patterns without "|" (or) *)
    let spat_list = norm spat [] in
    let pat_list = List.map pattern spat_list in
    let pat = orpat pat_list in
    (* the flag [zero] is true when [is_cont] is true *)
    let _, b = block signals b in
    { m_pat = pat; m_body = b; m_env = h0; 
      m_reset = false; m_zero = true } in
    
  (* first build the two association tables *)
  let exps = unique handler_list in
  (* compile each of them *)
  (* produces the expression to match *)
  let e = match exps with 
    | [e] -> exp signals e | _ -> tuple (List.map (exp signals) exps) in
  (* produces the handlers *)
  let pat_block_list = List.map (pattern exps) handler_list in
  (* treat the optional default handler *)
  let total, pat_block_list =
    match b_opt with
    | None -> false, pat_block_list
    | Some(b) ->
       let _, b = block signals b in
       true, pat_block_list @ 
	       [{ m_pat = { Zaux.wildpat with p_typ = e.e_typ }; m_body = b; 
		  m_env = Env.empty; m_reset = false; m_zero = false }] in
  (eq_match total e pat_block_list) :: eq_list

let implementation impl =
  match impl.desc with
    | Eopen _ | Etypedecl _ -> impl
    | Econstdecl(n, is_static, e) ->
       let e = exp Env.empty e in
       { impl with desc = Econstdecl(n, is_static, e) }
    | Efundecl(n, ({ f_args = p_list; f_body = e; f_env = f_env } as body)) ->
        let signals, _, f_env = build Env.empty f_env in
	let p_list = List.map (pattern signals) p_list in
	let e = exp signals e in
	{ impl with desc = 
		      Efundecl(n, { body with f_args = p_list; 
					      f_body = e;
					      f_env = f_env }) }

let implementation_list impl_list = Misc.iter implementation impl_list

