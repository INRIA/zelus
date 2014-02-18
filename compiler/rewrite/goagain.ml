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
(* add goagain wires to present statements in continuous contexes *)

(* Augment a present containing at least a weak transition with a "goagain"
   wire that request a subsequent and immediate discrete reaction.

   The following changes are made:

   1. To every continuous function is added a new output:
        goagain = goagain_1 || ... || goagain_n

      Defined as the disjunction of the individual goagains within
      the block.

   2. To every instantiation of a continuous function must be added
      a goagain_r variable to accept the new output and include it
      in the disjunction for the block.

   3. To every present is added a goagain_p
      variable. It is set to true on the discrete transition.

      I.e.,
        present
        | z1 -> do D done
        | ...
        else D'

      becomes, roughly:

        present
        | z1 -> do D and goagain = true
        | ...
        else D' and goagain = false

      together with the goagains introduced recursively in D'.

   The structure of lets in the code have been normalised by letin. So we can
   assume that all definitions inside a continuous block are of the following form:

      result = f (x_1, ..., x_n)

   and will not occur as a sub-expression of another definition.

   This transformation is necessary only when at least one discrete register
   is modified in D.

 *)

open Misc
open Location
open Ident
open Zelus
open Deftypes

(* Contexts *)

type goagains = Ident.t State.t (* the set of all gogain variables *)

let merge goagains_list = List.fold_left State.pair State.empty goagains_list

let goagain_tentry () =
  { Deftypes.t_sort = Deftypes.ValDefault(Ebool(false));
    Deftypes.t_typ  = Initial.typ_bool; }

let env_from_goagains env goagains =
  State.fold (fun i -> Env.add i (goagain_tentry ()) ) goagains env

(* Utility functions *)
let eqmake desc = { eq_desc = desc; eq_loc = no_location }

let emake desc ty = { e_desc = desc; e_loc = no_location; e_typ = ty }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty }
let eqmake p e = eqmake (EQeq(p, e))

let ctrue = emake (Econst(Ebool(true))) Initial.typ_bool
let cfalse = emake (Econst(Ebool(false))) Initial.typ_bool

let conj e1 e2 =
  emake (Eapp (Eop (Lident.Modname (Initial.pervasives_name "&&")), [e1; e2]))
        Initial.typ_bool

let disj e1 e2 =
  emake (Eapp (Eop (Lident.Modname (Initial.pervasives_name "||")), [e1; e2]))
        Initial.typ_bool
let disj_list e_list =
  match e_list with
  | [] -> cfalse
  | e :: e_list -> List.fold_left disj e e_list

let pairpat p1 p2 = 
  pmake (Etuplepat([p1; p2]))
    (Deftypes.make (Deftypes.Tproduct [p1.p_typ; p2.p_typ]))

let var n = emake (Elocal(n)) Initial.typ_bool
let varpat n = pmake (Evarpat(n)) Initial.typ_bool

let cunit = emake (Econst Evoid) Initial.typ_unit
let tuple l =
  match l with 
    | [] -> cunit
    | [e] -> e 
    | l -> emake (Etuple(l)) (Types.product (List.map (fun { e_typ = ty } -> ty) l))

let empty_block = 
  { b_vars = []; b_locals = []; b_body = []; 
    b_loc = no_location; b_env = Env.empty; b_write = Total.empty }

(** An automataon is weak if it contains at least one weak transition *)
let weak state_handler_list =
  let weak { s_until = su } = su <> [] in List.exists weak state_handler_list

(* Translate an equation. [equation (goagains, eq_list) eq = goagains', eq_list'] *)
(* [goagains] and [eq_list] are the already computed *)
(* list of [goagain] variables and list of equations to which the results are added *)
let rec equation (goagains, eq_list) ({ eq_desc = desc } as eq) =
  match desc with
    | EQeq(p, ({ e_desc = (Eapp(Eop(f), _)) } as e)) 
        when Types.is_a_hybrid_node f ->
        (* [p = f(e1,..., en)] becomes [(go, p) = f(e1,..., en)] *)
        let go = Ident.fresh "goagain" in
        let new_eq = { eq with eq_desc = EQeq(pairpat (varpat go) p, e) } in
        State.cons go goagains,
        new_eq :: eq_list
    | EQeq _ | EQder _ | EQinit _ | EQemit _ | EQnext _ -> 
        goagains, eq :: eq_list
    | EQmatch(total, e, m_h_list) ->
        let go = Ident.fresh "goagain" in
        let m_h_used_list = List.map (match_handler go) m_h_list in
        if List.exists (fun (_, u) -> u) m_h_used_list
        then
          let m_h_list = List.map (complete_match_handler go) m_h_used_list in
          State.cons go goagains,
          { eq with eq_desc = EQmatch(total, e, m_h_list) } :: eq_list
        else
          goagains, eq :: eq_list
    | EQreset(b, e) ->
        let goagains, b = block_single goagains b in
        goagains, { eq with eq_desc = EQreset(b, e) } :: eq_list
    | EQpresent(p_h_list, b_opt) ->
	  let go = Ident.fresh "goagain" in
          let b_opt = 
	    Misc.optional_map (fun b -> let b, _ = block go b in b) b_opt in
	  let p_h_list = List.map (present_handler go) p_h_list in
          State.cons go goagains,
          { eq with eq_desc = EQpresent(p_h_list, b_opt) } :: eq_list
    | EQautomaton _ -> assert false
        
and equation_list goagains eq_list = List.fold_left equation (goagains, []) eq_list

and local ({ l_eq = eq_list; l_env = env } as l) =
  let goagains, eq_list = equation_list State.empty eq_list in
  let env = env_from_goagains env goagains in
  goagains, { l with l_eq = eq_list; l_env = env; }

(* [block go b] compiles a block. It returns a new block and a bit [bit] *)
(* [bit = true] means that there is a goagain inside *)
and block go ({ b_vars = n_list; b_body = eq_list; b_env = n_env } as b) =
  (* [adds local go1,..., gon in ...] *)
  let add_locals goagains n_list n_env =
    let add go (n_list, n_env) = go :: n_list, Env.add go (goagain_tentry ()) n_env in
    State.fold add goagains (n_list, n_env) in
  
  let goagains, eq_list = equation_list State.empty eq_list in
  if State.is_empty goagains then b, false
  else
    let go_list = State.fold (fun i l -> var i :: l) goagains [] in
    let new_eq = eqmake (varpat go) (disj_list go_list) in
    let n_list, n_env = add_locals goagains n_list n_env in
    { b with b_vars = n_list; b_body = new_eq :: eq_list; b_env = n_env }, true

(** for a single block (e.g., that appear under a reset), there is no use to *)
(** introduce extra local variables for goagain variables *)
and block_single goagains ({ b_body = eq_list } as b) =
  let goagains, eq_list = equation_list goagains eq_list in
  goagains, { b with b_body = eq_list }

and complete_block go (({ b_body = eq_list } as b), complete) =
  if complete then b 
  else { b with b_body = (eqmake (varpat go) cfalse) :: eq_list }

and match_handler go ({ m_body = b } as m_h) =
  let b, complete = block go b in
  { m_h with m_body = b }, complete

and complete_match_handler go ({ m_body = b } as m_h, complete) =
  { m_h with m_body = complete_block go (b, complete) }

and present_handler go ({ p_body = b } as p_h) =
  (* add an equation [go = true] in the block *)
  let new_eq = eqmake (varpat go) ctrue in
  { p_h with p_body = { b with b_body = new_eq :: b.b_body } }

(** Prepare the output *)
(** [outputs [go1;...;gon] e = go1 or ... or gon, e] *)
let outputs goagains e =
  let go_list = State.fold (fun i l -> var i :: l) goagains [] in
  tuple [disj_list go_list; e]

(** Translation of a normalized expression. *)
(** Once normalised, it is either of the form [e] with no more *)
(** stateful applications inside or a [let L in e] *)
let rec exp ({ e_desc = desc } as e) =
  match desc with
    | Elet(l, e1) ->
        let goagains, l = local l in
        let o = outputs goagains e1 in
        { e with e_desc = Elet(l, o) }
    | _ -> outputs State.empty e

let implementation impl =
  match impl.desc with
  | Efundecl(f,
      ({ f_kind = C; f_args = p_list; f_body = e; } as body)) ->
        let e = exp e in
        { impl with desc = Efundecl(f, { body with f_body = e }) }
  | _ -> impl
        
let implementation_list impl_list = Misc.iter implementation impl_list
