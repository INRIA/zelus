(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
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
open Zelus
open Aux
open Mapfold

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
(*   | P(p1), ..., true, ... -> (* zero = true *) ...                   *)
(*   | P(p3), ..., _,  true -> (* zero = true *) ...                    *)
(*   end                                                                *)
(* the bit [zero] indicates that the branch corresponds to a *)
(* zero-crossing. It is set to [true] only when the context is continuous *)
(*                                                                      *)
(*                                                                      *)
(* a signal x is represented by a P(v) (present) or A (absent)          *)

(* representation of signals. A [signal] is represented as an optional value *)
let present_name = Lident.Modname(Initial.stdlib_name "P")
let absent_name = Lident.Modname(Initial.stdlib_name "A")
let emit e = Aux.constr1 present_name [e]
let absent = Aux.constr0 absent_name

let presentpat pat = Aux.pmake (Econstr1pat(present_name, [pat]))
let absentpat = Aux.pmake (Econstr0pat(absent_name))

(* implementation of the presence test ? of a signal *)
(* match e with P _ -> true | A -> false *)
let test e =
  Aux.e_match true e [match_handler (presentpat wildpat) etrue;
                      match_handler absentpat efalse]
    
(* Equality between expressions. for efficiency reasons *)
(* we restrict to simple cases *)
let equal e1 e2 =
  match e1.e_desc, e2.e_desc with
    | Econst(i), Econst(j) when (i = j) -> true
    | (Evar(i), Evar(j)) | (Elast { id = i }, Elast { id = j }) -> true
    | _ -> false

(* the member function *)
let mem e exps = List.exists (equal e) exps

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

(* compute the set of expressions from a signal pattern matching *)
(* expressions appearing more than once are shared *)
let unique handler_list =
  let rec unique exps spat =
    match spat.desc with
    | Econdand(spat1, spat2) | Econdor(spat1, spat2) -> 
       unique (unique exps spat1) spat2
    | Econdexp(e) | Econdpat(e, _) ->
       if mem e exps then exps
       else e :: exps
    | Econdon(spat1, e) ->
       unique (if mem e exps then exps else e :: exps) spat1 in
  
  List.fold_left
    (fun exps { p_cond = spat } -> unique exps spat) [] handler_list

(* normalize a signal pattern *)
let rec norm ({ desc } as spat) acc =
  match desc with
  | Econdor(spat1, spat2) -> norm spat1 (norm spat2 acc)
  | Econdpat _ | Econdexp _ | Econdand _ | Econdon _ -> spat :: acc

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
    Not_found -> Aux.wildpat :: cont

(* build the pattern *)
let pattern exps { p_cond; p_body; p_env } =
  let pattern spat =
    let pat_list = List.fold_right (pat spat) exps [] in
    match pat_list with
    | [] -> assert false
    | [pat] -> pat
    | _ -> tuplepat(pat_list) in
  (* extract the list of simple signals patterns without "|" (or) *)
  let spat_list = norm p_cond [] in
  let pat_list = List.map pattern spat_list in
  let pat = orpat pat_list in
  { m_pat = pat; m_body = p_body; m_env = Env.empty; m_loc = no_location; 
    m_reset = false; m_zero = true }

(* add a default value for signals. *)
(* [local ..., x, ...] becomes [local ..., x default A, ...] *)
let add_absent_vardec acc ({ var_name } as v) =
  if S.mem var_name acc then
    { v with var_default = Some(absent) }, S.remove var_name acc
  else v, acc

(* Translating a present statement *)
(* a present statement is translated into a pattern-matching *)
let generic_present_handlers e_match handlers default_opt =
  (* build the two association tables *)
  let exps = unique handlers in
  (* produces the expression to match *)
  let e = match exps with | [e] -> e | l -> Aux.tuple l in
  (* produces the handlers *)
  let pat_e_list = List.map (pattern exps) handlers in
  (* treat the optional default handler *)
  let is_total, default_handler =
    match default_opt with
    | NoDefault -> false, []
    | Init(e) ->
       true, [match_handler wildpat e]
    | Else(e) -> true, [match_handler wildpat e] in
  e_match is_total e (pat_e_list @ default_handler)

let present_handlers handlers default_opt =
  generic_present_handlers Aux.e_match handlers default_opt

let eq_present_handlers handlers default_opt =
  generic_present_handlers Aux.eq_match handlers default_opt

(* [acc] is the set of variables [id] in [eq] that contains an *)
(* equation [emit id = ...] *)
let equation funs acc eq =
  let { eq_desc }, acc = Mapfold.equation funs acc eq in
  match eq_desc with
  | EQpresent { handlers; default_opt } ->
     eq_present_handlers handlers default_opt, acc
  | EQemit(id, e_opt) ->
  (* [emit id = e] is replaced by [id = P(e)] *)
     let e = match e_opt with | None -> Aux.evoid | Some(e) -> e in
     Aux.id_eq id (emit e), S.add id acc
  | _ -> raise Mapfold.Fallback

and expression funs acc e =
  let { e_desc }, acc = Mapfold.expression funs acc e in
  match e_desc with
  | Epresent { handlers; default_opt } ->
     present_handlers handlers default_opt, acc
  | Eop(Etest, [e]) ->
     test e, acc
  | _ -> raise Mapfold.Fallback

and block funs acc b =
  let ({ b_vars } as b), acc = Mapfold.block funs acc b in
  let b_vars, acc = Util.mapfold add_absent_vardec acc b_vars in
  { b with b_vars }, acc

let program _ p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with equation; expression; global_funs } in
  let { p_impl_list } as p, _ = Mapfold.program_it funs S.empty p in
  { p with p_impl_list = p_impl_list }

