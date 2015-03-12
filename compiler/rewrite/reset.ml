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

(* Distribution of reset under match/with constructs *)
(* The transformation is applied on normalized expressions *)
(* A reset [z] is of the form: Zinit(i) | Zelse(i) *)
(* Zinit(i) means that [i = true -> false] *)
(* Zelse(i) means that [i] can be true anywhere *)
(* reset E every Zinit(i) = E since E is supposed to start fresh *)
(* reset E every Zelse(i) = reset E every i *)
(* Translation: *)
(* 1/ reset(z)(match e with | C1 -> ... | C2 -> ...) =
         reset init i1 = true every z
         and
         reset init i2 = true every z
         and match e with
             | C1 -> reset(last i1)(...) and i1 = false
             | C2 -> reset(last in)(...) and in = false
         end
   2/ reset(z)(E1 and ... and En) = reset(z)(E1) and ... and reset(z)(En)
   3/ reset(z)(x = op(e)) = x = op(e) if op is combinatorial
   4/ reset(z)(x = f(e)) = reset x = f(e) every z otherwise
   5/ reset(z)(reset E every k) = reset(z or k)(E)
   6/ reset(z)(init x = e) = reset init x = e every z if e is constant
   7/ reset(z)(init x = e) = reset init x = e every (true -> z) otherwise
   8/ reset(z)(x = e1 -> e2) = x = if z then e1 else e2
   9/ reset(z)(init) = z (* init is a clock *)

*)

open Misc
open Location
open Deftypes
open Zelus
open Ident

type reset = 
  | Zinit of Ident.t (* Zinit(i): the reset bit is [i = true -> false] *)
  | Zelse of exp (* Zelse(e): the reset bit is e *)

(** Build basic operations *)
let make desc ty = 
  { e_desc = desc; e_loc = no_location; e_typ = ty; e_caus = [] }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty; p_caus = [] }
let boolpat n = pmake (Evarpat(n)) Initial.typ_bool
let eqmake desc =
  { eq_desc = desc; eq_loc = no_location; eq_before = S.empty;
    eq_after = S.empty; eq_write = Deftypes.empty }
let initmake n e =
  { eq_desc = EQinit(n, e); eq_loc = no_location;
    eq_before = S.empty; eq_after = S.empty; eq_write = Deftypes.empty }
let setmake n e = 
  { eq_desc = EQeq(boolpat n, e); eq_loc = no_location;
    eq_before = S.empty; eq_after = S.empty; eq_write = Deftypes.empty }
let efalse = make (Econst(Ebool(false))) Initial.typ_bool
let etrue = make (Econst(Ebool(true))) Initial.typ_bool
let eqfalse i =
  { eq_desc = EQeq(boolpat i, efalse); eq_loc = no_location;
    eq_before = S.empty; eq_after = S.empty; eq_write = Deftypes.empty }
let boollast i = make (Elast(i)) Initial.typ_bool
let add_false_to_block i ({ b_body = eq_list } as b) =
  { b with b_body = eqfalse i :: eq_list }
let ifthenelse e1 e2 e3 =
  { e2 with e_desc = Eapp(Eifthenelse, [e1; e2; e3]) }
let or_op e1 e2 = 
  make (Eapp(Eop(false, Lident.Modname(Initial.pervasives_name "||")), [e1; e2])) 
    Initial.typ_bool
let init i eq_list = 
  (initmake i etrue) :: (setmake i efalse) :: eq_list
let reset = function | Zinit(i) -> boollast i | Zelse(e) -> e
let initial = function | Zinit _ -> true | Zelse _ -> false
let eqinit i = function
  | Zinit _ -> initmake i etrue 
  | Zelse(e) -> eqmake (EQreset([initmake i etrue], e))
let zor e = function
  | Zinit _ -> e | Zelse(ze) -> or_op ze e

(** Distribute [before] and [after] fields over a list of equations *)
(** Only unsafe equations are concerned *)
let before_after before after eq_list acc =
  let add acc ({ eq_before = before0; eq_after = after0 } as eq) =
    { eq with eq_before =
	if S.is_empty before0 then before0 else S.union before0 before;
      eq_after =
	if S.is_empty after0 then after0 else S.union after0 after } :: acc in
  List.fold_left add acc eq_list
  
(** Static expressions *)
let rec static { e_desc = desc } =
  match desc with
  | Econst _ | Econstr0 _ -> true
  | Etuple(e_list) -> List.for_all static e_list
  | Erecord(qual_e_list) -> List.for_all (fun (_, e) -> static e) qual_e_list
  | Erecord_access(e, _) -> static e
  | _ -> false


(** Translation of equations. From bottom to top. *)
(** [equation res (eq_list, env) eq = eq_list', env'] *)
(** returns an extended set of equations with env extended accordingly *)
let rec equation res (eq_list, env)
    ({ eq_desc = desc; eq_before = before; eq_after = after } as eq) =
  match desc with
  | EQeq(p, ({ e_desc = Eapp(Eop(inline, f), e_list) } as e)) 
       when (Types.is_a_node f) && not (initial res) ->
     (* turn the application into [p = f(e1,...,en) every res] *)
     let e_list = (reset res) :: e_list in
     { eq with eq_desc = 
		 EQeq(p, { e with e_desc = Eapp(Eevery(inline, f), e_list) }) }
       :: eq_list, env
  | EQeq(p, ({ e_desc = Eapp(Eevery(inline, f), e_res :: e_list) } as e)) 
       when (Types.is_a_node f) && not (initial res) ->
     (* turn the application into [p = f(e1,...,en) every res or e_res] *)
     let e_list = (zor e_res res) :: e_list in
     { eq with eq_desc = 
		 EQeq(p, { e with e_desc = Eapp(Eevery(inline, f), e_list) }) }
       :: eq_list, env
  | EQeq(p, { e_desc = Eapp(Eminusgreater, [e1; e2]) }) -> 
     (* [e1 -> e2 = if res then e1 else e2] *)
     { eq with eq_desc = EQeq(p, ifthenelse (reset res) e1 e2) } :: eq_list, env
  | EQeq(p, { e_desc = Eapp(Einitial, []) }) -> 
     (* [init = res] *)
     { eq with eq_desc = EQeq(p, reset res) } :: eq_list, env
  | EQset _ -> eq :: eq_list, env
  | EQinit(x, e) when not (static e) || not (initial res) -> 
     { eq with eq_desc = EQreset([eq], reset res) } :: eq_list, env
  | EQnext _ | EQder _ | EQeq _ | EQinit _ -> eq :: eq_list, env     
  | EQmatch(total, e, m_h_list) ->
     (* introduce [n] initialization registers *)
     (* [init i_1 = true and ... init i_n = true] *)
     (* distribute the new reset bit [last i_k] in every handler *)
     (* and add [i_k = false] in every handler *)
     let i_list =
       List.map (fun _ -> Ident.fresh "init") m_h_list in
     let env =
       List.fold_left 
         (fun acc i -> Env.add i { t_typ = Initial.typ_bool; 
				   t_sort = Mem discrete_memory } acc)
	 env i_list in
     let eq_list =
       List.fold_left (fun acc i -> (eqinit i res) :: acc) eq_list i_list in
     (* then compile the body *)
     let m_h_list =
       List.map2
         (fun ({ m_body = b } as h) i -> 
	  { h with m_body = 
		     add_false_to_block i (block (Zelse(boollast i)) b) }) 
         m_h_list i_list in
     { eq with eq_desc = EQmatch(total, e, m_h_list) } :: eq_list, env
  | EQreset(res_eq_list, e) ->
     (* The construction [reset eq1 and ... and eqn every e] is distributed *)
     (* among the [eq1;...; eqn] *)
    (* scheduling information ([before] and [after] fields) must *)
    (* be added to every equation *)
    let res_eq_list, env = equation_list (Zelse (zor e res)) env res_eq_list [] in
    before_after before after res_eq_list eq_list, env
  | EQemit _ | EQautomaton _ | EQpresent _ | EQblock _ -> assert false

and equation_list res env eq_list acc_list = 
  List.fold_left (equation res) (acc_list, env) eq_list

and local res ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, l_env = equation_list res l_env eq_list [] in
  { l with l_eq = eq_list; l_env = l_env }

(** translation of blocks *)
and block res ({ b_vars = n_list; b_body = eq_list; b_env = n_env } as b) =
  (* add local declarations [local x1 in ... in local xn in ...] *)
  let add_locals env n_list n_env =
    let add x entry (n_list, n_env) = x :: n_list, Env.add x entry n_env in
    Env.fold add env (n_list, n_env) in
    
  let eq_list, env = equation_list res Env.empty eq_list [] in
  let n_list, n_env = add_locals env n_list n_env in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }

(** The main entry function for expressions. They are supposed to be normalized *)
let exp ({ e_desc = desc } as e) =
  (* add an equation [init i = true and i = false] *)
  let add_initialization_bit i ({ l_eq = eq_list; l_env = l_env }  as l) =
    let l_env = Env.add i { t_typ = Initial.typ_bool; 
			    t_sort = Mem discrete_memory } l_env in
    let eq_list = init i eq_list in
    { l with l_eq = eq_list; l_env = l_env } in
  match desc with
    | Elet(l, e) -> 
       (* introduce the initialization bit [i = true -> false] *)
       let i = Ident.fresh "init" in
       let l = local (Zinit(i)) l in
       let l = add_initialization_bit i l in
       { e with e_desc = Elet(l, e) }
    | _ -> e
        
let implementation impl =
  match impl.desc with
      | Efundecl(n, ({ f_kind = D | C; f_body = e } as body)) ->
        { impl with desc = Efundecl(n, { body with f_body = exp e }) }
      | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl _ -> impl
      

let implementation_list impl_list = Misc.iter implementation impl_list

