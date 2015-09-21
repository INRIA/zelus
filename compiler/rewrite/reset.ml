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
open Zaux
open Ident

let eq_false i = eqmake (EQeq(bool_varpat i, efalse))

let add_false_to_block i ({ b_body = eq_list } as b) =
  { b with b_body = eq_false i :: eq_list }

type reset = 
  | Zinit of Ident.t (* Zinit(i): the reset bit is [i = true -> false] *)
  | Zelse of exp (* Zelse(e): the reset bit is e *)

let reset = function | Zinit(i) -> bool_last i | Zelse(e) -> e
let initial = function | Zinit _ -> true | Zelse _ -> false
let eqinit i = function
  | Zinit _ -> eq_init i etrue 
  | Zelse(e) -> eqmake (EQreset([eq_init i etrue], e))
let zor e = function
  | Zinit _ -> e | Zelse(ze) -> or_op ze e

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
let rec equation res (eq_list, env) ({ eq_desc = desc } as eq) =
  match desc with
  | EQeq(p, e) ->
     { eq with eq_desc = EQeq(p, expression res e) } :: eq_list, env
  | EQset(n, e) ->
     { eq with eq_desc = EQset(n, expression res e) } :: eq_list, env
  | EQinit(x, e) ->
     let eq =
       if not (static e) || not (initial res) then
	 { eq with eq_desc = EQreset([eq], reset res) } else eq in
     eq :: eq_list, env
  | EQder(x, e, None, []) ->
     { eq with eq_desc = EQder(x, expression res e, None, []) } :: eq_list, env
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
				   t_sort = Deftypes.memory } acc)
	 env i_list in
     let eq_list =
       List.fold_left (fun acc i -> (eqinit i res) :: acc) eq_list i_list in
     (* then compile the body *)
     let m_h_list =
       List.map2
         (fun ({ m_body = b } as h) i -> 
	  { h with m_body = 
		     add_false_to_block i (block (Zelse(bool_last i)) b) }) 
         m_h_list i_list in
     { eq with eq_desc = EQmatch(total, e, m_h_list) } :: eq_list, env
  | EQreset(res_eq_list, e) ->
    (* The construction [reset eq1 and ... and eqn every e] is distributed *)
    (* among the [eq1;...; eqn] *)
    equation_list (Zelse (zor e res)) env res_eq_list eq_list
  | EQblock _ | EQemit _ | EQnext _ | EQder _
  | EQautomaton _ | EQpresent _ -> assert false

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

(** translation of expressions *)
and expression res ({ e_desc = desc } as e) =
  match desc with
  | Elocal _ | Eglobal _ | Econst _ | Econstr0 _ | Elast _ -> e
  | Eapp(Eminusgreater, [e1; e2]) -> 
     (* [e1 -> e2 = if res then e1 else e2] *)
     ifthenelse (reset res) e1 e2
  | Eapp(Einitial, []) -> 
     (* [init = res] *)
     reset res
  | Eapp(Eop(is_inline, f) as op, e_list) ->
     let e_list = List.map (expression res) e_list in
     if (Types.is_a_node f) && not (initial res) then
       (* turn the application into [f(e1,...,en) every res] *)
       { e with e_desc = Eapp(Eevery(is_inline, f), (reset res) :: e_list) }
     else 
       { e with e_desc = Eapp(op, e_list) }
  | Eapp(Eevery(is_inline, f) as op, e_res :: e_list) ->
     let e_res = expression res e_res in
     let e_list = List.map (expression res) e_list in
     if (Types.is_a_node f) && not (initial res) then
       (* turn the application into [f(e1,...,en) every res] *)
       { e with e_desc = Eapp(Eevery(is_inline, f),
			      (or_op (reset res) e_res) :: e_list) }
     else { e with e_desc = Eapp(op, e_res :: e_list) }
  | Eapp(op, e_list) ->
     { e with e_desc = Eapp(op, List.map (expression res) e_list) }
  | Etuple(e_list) ->
     { e with e_desc = Etuple(List.map (expression res) e_list) }
  | Erecord_access(e, x) ->
     { e with e_desc = Erecord_access(expression res e, x) }
  | Erecord(l_e_list) ->
     let l_e_list = List.map (fun (l, e) -> (l, expression res e)) l_e_list in
     { e with e_desc = Erecord(l_e_list) }
  | Etypeconstraint(e, ty) ->
     { e with e_desc = Etypeconstraint(expression res e, ty) }
  | Eseq(e1, e2) ->
     { e with e_desc = Eseq(expression res e1, expression res e2) }
  | Elet _ | Eperiod _ | Epresent _ | Ematch _ -> assert false


(* introduce the initialization bit [init i = true and i = false] *)
let exp_with_reset ({ e_desc = desc } as e) =
  (* transform [e] into let rec init i = true and i = false
                            and result = Tr(i)(e) in result *)
  let add_init i ({ l_eq = eq_list; l_env = l_env } as l) =
    { l with l_eq = init i eq_list;
	     l_env = Env.add i
			     { t_typ = Initial.typ_bool; t_sort = Deftypes.memory }
			     l_env } in
  
  let i = Ident.fresh "init" in
  match desc with
  | Elet(l, e) ->
     let l = local (Zinit(i)) l in
     let e = expression (Zinit(i)) e in
     { e with e_desc = Elet(add_init i l, e) }
  | _ -> e
 
let implementation impl =
  match impl.desc with
      | Efundecl(n, ({ f_kind = D | C; f_body = e } as body)) ->
         { impl with desc =
		       Efundecl(n, { body with f_body = exp_with_reset e }) }
      | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl _ -> impl
      

let implementation_list impl_list = Misc.iter implementation impl_list

