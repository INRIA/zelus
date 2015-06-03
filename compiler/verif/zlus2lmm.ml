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

(* Translation into Lustre-- *)

(* no automaton, no present, no pre/fby/->. All names must be *)
(* pair-wise differents *)

(* Tr(ck)(res)(match e with
               | p1 -> E1 | ... | pn -> En) = 

   with one defined variable y (defnames = {y}) and used variable x
   (example: E1 = local t in do t = x + 3 and y = t + 2 done)

becomes:
 
   local c in
   do
     c = Tr(ck)(e)
   and
     Tr(c on c1)(E1)[y_1/y]
   and
     ...
   and
     Tr(c on cn)(En)[y_n/y]
   and
     c1 = test(p1)(c) and ... and cn = test(pn)(c)
   and
     pat(p1) = c and ... and pat(pn) = c
   and
     y = if c1 then y_1 else ... if cn then y_n [else pre y]

where:

  test(p)(c) returns an expression testing that the pattern p matches c
  pat(p) returns a pattern with variables only

Tr(ck)(x = e) = x = if ck then Tr(ck)(e) else pre x
                with the special case that if base then e else e' = e

*)

   
open Location
open Ident
open Zelus
open Deftypes

let vardec id ty =
  { Lmm.p_kind = Lmm.Evar; Lmm.p_name = id;
    Lmm.p_typ = ty; Lmm.p_loc = no_location }

let eq_make pat e = 
  { Lmm.eq_lhs = pat; Lmm.eq_rhs = e; Lmm.eq_loc = no_location }
    		  
let e_true = Lmm.Econst(Ebool(true))
let e_false = Lmm.Econst(Ebool(false))
		   
let bool_op op e1 e2 =
  Lmm.Eapp(Lmm.Eop(Lident.Modname(Initial.pervasives_name op)),[e1; e2])
       
let equal_op e1 e2 = bool_op "=" e1 e2
let and_op e1 e2 =
  if e1 = e_true then e2
  else if e2 = e_true then e1
  else bool_op "&&" e1 e2
let or_op e1 e2 =
  if e1 = e_false then e2
  else if e2 = e_false then e1
  else bool_op "||" e1 e2
let ifthenelse e1 e2 e3 =
  Lmm.Eapp(Lmm.Eifthenelse, [e1; e2; e3])
let unarypre x = Lmm.Eapp(Lmm.Eunarypre, [Lmm.Elocal(x)])
			 
type ck = | Ck_base | Ck_on of ck * Lmm.exp
type res = | Res_never | Res_else of res * Lmm.exp
				      
let on ck c = Ck_on(ck, Lmm.Elocal(c))
let relse res c = Res_else(res, c)

(* from a clock to a boolean expression *)
let rec clock = function
  | Ck_base -> e_true
  | Ck_on(Ck_base, e) -> e
  | Ck_on(ck, e) -> and_op (clock ck) e

(* from a reset to a boolean expression *)
let rec reset = function
  | Res_never -> e_false
  | Res_else(Res_never, e) -> e
  | Res_else(res, e) -> or_op (reset res) e

type eqs = { eqs: Lmm.eq list; env: Lmm.vardec list; assertion: Lmm.exp list }

let empty = { eqs = []; env = []; assertion = []  }
	      
(* for a pair [pat, e] computes the equation [pat_v = e] and boolean *)
(* condition c where [pat_v] is only made of variables and [c] *)
(* is true when [pat] matches [e] *)
let rec filter ({ eqs = eqs; env = env} as acc) { p_desc = p_desc } e =
  match p_desc with
  | Ewildpat ->  acc, e_true
  | Evarpat(id) ->
     { acc with eqs = (eq_make (Lmm.Evarpat(id)) e) :: eqs }, e_true
  | Econstpat(c) -> acc, equal_op (Lmm.Econst(c)) e
  | Econstr0pat(c) -> acc, equal_op (Lmm.Econstr0(c)) e
  | Etuplepat(p_list) ->
     (* introduce n fresh names *)
     let n_ty_list =
       List.map (fun { p_typ = ty } -> Ident.fresh "", ty) p_list in
     let e_list = List.map (fun (n, _) -> Lmm.Elocal(n)) n_ty_list in
     let env =
       List.fold_left
	 (fun env (n, ty) -> (vardec n ty) :: env) env n_ty_list in
     filter_list { acc with env = env } p_list e_list
  | Ealiaspat(p, id) ->
     let ({ eqs = eqs } as acc), cond = filter acc p e in
     { acc with eqs = (eq_make (Lmm.Evarpat(id)) e) :: eqs }, cond
  | Etypeconstraintpat(p, _) -> filter acc p e
  | Eorpat(p1, p2) ->
     let acc, cond1 = filter acc p1 e in
     let acc, cond2 = filter acc p2 e in
     acc, or_op cond1 cond2
  | Erecordpat(l_p_list) ->
     let acc, cond =
       List.fold_left
	 (fun (acc, cond) (l, p) ->
	  let acc, cond_l_p = filter acc p (Lmm.Erecord_access(e, l)) in
	  acc, and_op cond cond_l_p) (acc, e_true) l_p_list in
     acc, cond

and filter_list acc p_list e_list =
  List.fold_left2
    (fun (acc, cond) p e ->
     let acc, cond_p_e = filter acc p e in
     acc, and_op cond cond_p_e) (acc, e_true) p_list e_list
     
(* translate an operator *)
(* a statefull function application receives a clock as an extra argument *)
let operator ck op e_list =
  match op with
  | Eifthenelse -> Lmm.Eapp(Lmm.Eifthenelse, e_list) 
  | Eop(_, lid) | Eevery(_, lid) ->
		   if Types.is_a_function lid then Lmm.Eapp(Lmm.Eop(lid), e_list)
		   else Lmm.Eapp(Lmm.Eop(lid), (clock ck) :: e_list)
  | Eunarypre | Eminusgreater | Efby | Eup | Einitial | Edisc
  | Etest -> assert false
		    
(* renaming of a name by an other *)
let rename x subst =
  try Env.find x subst
  with | Not_found -> x (* assert false *)
			     
(* the set of shared variables from a set of defined names *)
let shared_variables { dv = dv } = dv
				     
(* returns the previous value of [x] *)
let pre x subst =
  try
    Lmm.Elocal(Env.find x subst) (* if [x] is given an last value [lx] *)
  with
  | Not_found -> unarypre x

(* returns the expression associated to [x] in a substitution [name_to_exp] *)
(* if [x] is unbound, returns either [lx] if [x in subst] or [pre x] *)
let get x name_to_exp subst =
  try
    Env.find x name_to_exp
  with
  | Not_found -> pre x subst

(* [subst] is a substitution to rename [last x] by a fresh variable [lx] *)
let rec expression ck subst { e_desc = desc } =
  match desc with
  | Elocal(id) -> Lmm.Elocal(id)
  | Eglobal(lid) -> Lmm.Eglobal(lid)
  | Econst(im) -> Lmm.Econst(im)
  | Econstr0(lid) -> Lmm.Econstr0(lid)
  | Elast(x) -> pre x subst
  | Eapp(op, e_list) ->
     operator ck op (List.map (expression ck subst) e_list)
  | Etuple(e_list) ->
     Lmm.Etuple(List.map (expression ck subst) e_list)
  | Erecord_access(e, lid) ->
     Lmm.Erecord_access(expression ck subst e, lid)
  | Erecord(l_e_list) ->
     Lmm.Erecord
       (List.map (fun (l, e) -> (l, expression ck subst e)) l_e_list)
  | Etypeconstraint(e, _) -> expression ck subst e
  | Epresent _ | Ematch _ | Elet _ | Eseq _ | Eperiod _ -> assert false
								  

(* [split s_set eqs = [eqs_acc, name_to_exp] splits eqs into *)
(* two complementary sets of equations *)
(* [name_to_exp] associates an expression to any names from [s_set] *)
let split s_set eqs =
  let split (eqs_acc, name_to_exp) ( { Lmm.eq_lhs = p; Lmm.eq_rhs = e } as eq) =
    match p with
    | Lmm.Evarpat(id) ->
       if S.mem id s_set then eqs_acc, Env.add id e name_to_exp
       else eq :: eqs_acc, name_to_exp
    | _ -> eq :: eqs_acc, name_to_exp in
  List.fold_left split ([], Env.empty) eqs

(* build a substitution from an environment *)
(* [build subst l_env = subst'] extends the *)
(* substitution [subst] with entries [x1\lx1,..., xn\lxn] *)
(* for all state variables which are initialized *)
let build subst ({ env = env } as acc) l_env =
  Env.fold
    (fun x { t_sort = sort; t_typ = ty } (subst, ({ env = env } as acc)) ->
     let subst = match sort with
       | Mem { t_initialized = true } ->
	  let lx = Ident.fresh "" in Env.add x lx subst
       | Val | ValDefault _ | Mem _ -> subst in
     subst, { acc with env = (vardec x ty) :: env })
    l_env (subst, acc)
    
(* [equation ck res subst acc eq = acc'] *)
(* with [acc = { eqs = eqs; env = env }]. Returns a set of *)
(* equations and an environment for names *)
let rec equation ck res subst
		 ({ eqs = eqs; env = env; assertion = assertion } as acc)
		 { eq_desc = desc; eq_write = defnames } = 
  match desc with
  | EQeq(p, e) ->
     let n = Ident.fresh "" in
     let ({ eqs = eqs; env = env } as acc), _ = filter acc p (Lmm.Elocal(n)) in
     { acc with
       eqs = (eq_make (Lmm.Evarpat(n)) (expression ck subst e)) :: eqs;
       env = (vardec n e.e_typ) :: env }
  | EQreset(eq_list, e) ->
     let e = expression ck subst e in
     equation_list ck (relse res e) subst acc eq_list
  | EQmatch(total, e, p_h_list) ->
     (* first translate [e] *)
     let e = expression ck subst e in
     (* then compute the set of shared variables *)
     let s_set = shared_variables defnames in
     (* introduce [n] fresh clock names [c1,..., cn] *)
     let c_list =
       List.map (fun _ -> Ident.fresh "") p_h_list in

     (* translate the list of body *)
     let equations_from_handler acc c { m_body = b } =
       let { eqs = eqs } as acc = block (on ck c) res subst acc b in
       let eqs, name_to_exp = split s_set eqs in
       { acc with eqs = eqs; env = env }, name_to_exp in
     
     let acc, cond_name_to_exp_list =
       List.fold_right2
	 (fun c p_h (acc, cond_name_to_exp_list) ->
	  let acc, name_to_exp = equations_from_handler acc c p_h in
	  acc, (c, name_to_exp) :: cond_name_to_exp_list)
	 c_list p_h_list (acc, []) in
     
     (* translate the list of patterns *)
     let patterns_from_handler acc c { m_pat = p } =
       let ({ eqs = eqs } as acc), cond = filter acc p e in
       { acc with eqs = (eq_make (Lmm.Evarpat(c)) cond) :: eqs } in
     let { eqs = eqs; env = env; assertion = assertion } =
       List.fold_left2 patterns_from_handler acc c_list p_h_list in

     (* the variables [c1,...,cn] cannot be true at the same time *)
     let assertion =
       Lmm.Eapp(Lmm.Esharp, List.map (fun c -> Lmm.Elocal(c)) c_list) ::
	 assertion in
     let env = List.fold_left
		 (fun acc c -> (vardec c Initial.typ_bool) :: acc) env c_list in
     
     (* merge results for every shared variable. Returns *)
     (* if c1 then e1 else ... en *)
     let rec merge x cond_name_to_exp_list =
       match cond_name_to_exp_list with
       | [] -> assert false
       | [cond, name_to_exp] -> get x name_to_exp subst
       | (cond, name_to_exp) :: cond_name_to_exp_list ->
	  Lmm.Eapp(Lmm.Eifthenelse,
		   [Lmm.Elocal(cond); get x name_to_exp subst;
		    merge x cond_name_to_exp_list]) in
     let eqs =
       S.fold
	 (fun x eqs ->
	  (eq_make (Lmm.Evarpat(x)) (merge x cond_name_to_exp_list)) :: eqs)
	 s_set eqs in
     { eqs = eqs; env = env; assertion = assertion }
  | EQinit(x, e) ->
     let unarypre_with_clock ck x lx =
       Lmm.Eapp(Lmm.Eunarypre,
		[ifthenelse (clock ck) (Lmm.Elocal(x)) (Lmm.Elocal(lx))]) in
     (* the initialization is reset every time [res] is true *)
     (* produce [last_x = if res then e else pre(if ck then x else last_x)] *)
     let e = expression ck subst e in
     let e = ifthenelse (reset res) e
       (unarypre_with_clock ck x (rename x subst)) in
     { acc with eqs = (eq_make (Lmm.Evarpat(rename x subst)) e) :: eqs }
  | EQnext _ | EQset _ | EQblock _ | EQemit _ | EQautomaton _
  | EQpresent _ | EQder _ -> assert false
									   
and equation_list ck res subst acc eq_list =
  List.fold_left (equation ck res subst) acc eq_list
 
and block ck res subst acc { b_body = body_eq_list; b_env = n_env } =
  let subst, acc = build subst acc n_env in
  equation_list ck res subst acc body_eq_list

let local ck res subst acc { l_eq = eq_list; l_env = l_env } =
  let subst, acc = build subst acc l_env in
  equation_list ck res subst acc eq_list
					
let let_expression ck res subst n_output
		   ({ eqs = eqs } as acc) ({ e_desc = desc } as e) =
  match desc with
  | Elet(l, e) ->
     let { eqs = eqs } as acc = local ck res subst acc l in
     let e = expression ck subst e in
     { acc with
       eqs = (eq_make (Lmm.Evarpat(n_output)) e) :: eqs }
  | _ ->
     let e = expression ck subst e in
     { acc with
       eqs = (eq_make (Lmm.Evarpat(n_output)) e) :: eqs }

let kind = function | A | AD -> Lmm.A | D -> Lmm.D | C -> assert false
							    
let implementation impl_list impl =
  match impl.desc with
  | Eopen _ -> impl_list
  | Etypedecl(n, params, td) ->
     { Lmm.desc = Lmm.Etypedecl(n, params, td);
       Lmm.loc = no_location } :: impl_list
  | Econstdecl(x, e) ->
     { Lmm.desc = Lmm.Econstdecl(x, expression Ck_base Env.empty e);
       Lmm.loc = no_location } :: impl_list
  | Efundecl(n, { f_kind = k; f_args = p_list; f_body = e }) ->
     let n_input_list = List.map (fun _ -> Ident.fresh "") p_list in
     let e_list = List.map (fun n -> Lmm.Elocal(n)) n_input_list in
     let acc, _ = filter_list empty p_list e_list in
     if acc.env = [] then (Printf.printf "Empty\n"; flush stdout);
     let input_list =
       List.map2 (fun n p -> vardec n p.p_typ) n_input_list p_list in
     let n_output = Ident.fresh "" in
     let output = vardec n_output e.e_typ in
     (* if [n] is combinatorial, then no reset nor clock is useful *)
     (* otherwise, two extra parameters are added to functions *)
     let ck, res, input_list =
       match k with
       | A | AD -> Ck_base, Res_never, input_list
       | D ->
	  let ck_name = Ident.fresh "" in
	  let res_name = Ident.fresh "" in
	  let ck_vardec = vardec ck_name Initial.typ_bool in
	  let res_vardec = vardec res_name Initial.typ_bool in
	  on Ck_base ck_name, relse Res_never (Lmm.Elocal(res_name)),
	  ck_vardec :: res_vardec :: input_list 
       | C -> assert false in
     if acc.env = [] then (Printf.printf "Empty\n"; flush stdout);
     let { eqs = eqs; env = env; assertion = assertion } =
       let_expression ck res Env.empty n_output acc e in
     if env = [] then (Printf.printf "Empty\n"; flush stdout);
     { Lmm.desc =
	 Lmm.Efundecl(n,
		      { Lmm.f_kind = kind k; Lmm.f_inputs = input_list;
			Lmm.f_outputs = [output]; Lmm.f_local = env;
			Lmm.f_body = eqs; Lmm.f_assert = assertion });
       Lmm.loc = no_location } :: impl_list
				   
       
let implementation_list impl_list =
  List.rev (List.fold_left implementation [] impl_list)
