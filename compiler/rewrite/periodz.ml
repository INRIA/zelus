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
(* elimation of periods. Translation into zero-crossing functions *)
(* Programs must be in equational normal form *)

open Misc
open Location
open Ident
open Lident
open Initial
open Deftypes
open Zelus

let typ_float = Initial.typ_float

let emake desc ty = { e_desc = desc; e_loc = no_location; e_typ = ty }
let pmake desc ty = { p_desc = desc; p_loc = no_location; p_typ = ty }
let eqmake desc = { eq_desc = desc; eq_loc = no_location }
let floatpat x = pmake (Evarpat(x)) typ_float
let floatvar x = emake (Elocal(x)) typ_float
let zerovar x = emake (Elocal(x)) typ_zero
let zeropat x = pmake (Evarpat(x)) typ_zero
let up x = emake (Eapp(Eup, [floatvar x])) Initial.typ_zero
let local env eq_list = 
  { l_eq = eq_list; l_env = env; l_loc = Location.no_location }
let minus e = emake (Eapp(Eop(Name("~-.")), [e])) e.e_typ
let floatconst f = emake (Econst(Efloat(f))) typ_float

let spat_of_zero ({ e_desc = desc; e_loc = loc } as e) = { desc = Econdexp(e); loc = loc }

let block_of_eq n_list n_env eq_list =
  { b_vars = n_list; b_locals = []; b_body = eq_list;
    b_loc = no_location; b_write = Total.empty; b_env = n_env }

let local env eq_list = { l_eq = eq_list; l_env = env; l_loc = no_location }

let is_compiled_with_period f = Global.period_desc (Modules.find_value f)

let compiled_with_period_error loc lname =
  Format.eprintf "%aPeriod linking error: the function@%s@was \
                  compiled with the -period option."
    output_location loc
    (Lident.modname lname);
  raise Misc.Error

(** Translation of periods. *)
(** The period [p] = [f1...fn (f'1... f'm)] is translated into: *)
(** rec present z ->                                            *)
(**       local y in                                            *)
(**       do y = f'1 fby ... fby f'm fby y                      *)
(**       and o = -. (f2 fby ... fby fn fby y) done             *)
(**     and der o = 1.0 done                                    *)
(** and init o = -f1 and z = up(o)                              *)
(** Notice: the shifting of the period would be useless if "init" would be *)
(** considered as a discrete clock and the derivative written: *)
(** der o = 1.0 restart ((encoding_of_period p) every (z or init)) *)

let shift { p_phase = l1; p_period = l2 } =
  match l1, l2 with
    | [], x :: l2 -> x, { p_phase = []; p_period = l2 @ [x] }
    | [x], _ -> x, { p_phase = []; p_period = l2 }
    | x :: l1, l2 -> x, { p_phase = l1; p_period = l2 }
    | [], [] -> assert false

let period env eq_list z p =
  let f1, { p_phase = l1; p_period = l2 } = shift p in
  let fby f rest = emake (Eapp(Efby, [floatconst f; rest])) typ_float in
  let y = Ident.fresh "p" in
  let o = Ident.fresh "p" in
  let env_y = Env.singleton y { t_sort = Val; t_typ = typ_float } in
  let env_o = 
    Env.add o { t_sort = Mem Deftypes.continuous_memory;
                t_typ = typ_float } env in
  let p2 = List.fold_right fby l2 (floatvar y) in
  let p1 = List.fold_right fby l1 (floatvar y) in
  let eq_list =
    (eqmake(EQpresent([{ p_cond = spat_of_zero (zerovar z); 
                         p_env = Env.empty; 
                         p_body = block_of_eq [y] env_y
        [eqmake(EQeq(floatpat y, p2)); 
         eqmake(EQeq(floatpat o, minus (p1)))] }],
		      None))) ::
      (eqmake(EQder(o, floatconst 1.0, None, []))) ::
      (eqmake(EQinit(floatpat o, minus (floatconst f1), None))) :: eq_list in
  up(o), eq_list, env_o

(*
let period p =
  let f1, { p_phase = l1; p_period = l2 } = shift p in
  let fby f rest = emake (Eapp(Efby, [floatconst f; rest])) typ_float in
  let y = Ident.fresh "p" in
  let o = Ident.fresh "p" in
  let z = Ident.fresh "p" in
  let env_y = Env.singleton y { t_sort = Val; t_typ = typ_float } in
  let env_o_z = 
    Env.add o { t_sort = Mem { m_kind = Tcont; m_initialized = true; 
                               m_last = true; m_info = Der(true) }; 
                t_typ = typ_float }
      (Env.singleton z { t_sort = Val; t_typ = Initial.typ_zero }) in
  let p2 = List.fold_right fby l2 (floatvar y) in
  let p1 = List.fold_right fby l1 (floatvar y) in
  let eq_o_z =
    [eqmake(Epresent([{ p_cond = spat_of_zero (zerovar z); 
                        p_env = Env.empty; 
                        p_block = block_of_eq [y] env_y [eqmake(Eeq(floatpat y, p2)); 
							 eqmake(Eeq(floatpat o, minus (p1)))]
		      }],
                     Some(block_of_der o (floatconst 1.0))));
     eqmake(Einit(floatpat o, minus (floatconst f1)));
     eqmake(Eeq(zeropat z, up(o)))] in
  Elet(local env_o_z eq_o_z, zerovar z)
*)

let rec exp ({ e_desc = desc; e_loc = loc } as e) =
  let desc = match desc with
    | Econst _ | Econstr0 _ | Eglobal _ | Elocal _ | Elast _ as desc -> desc 
    | Etuple(e_list) -> Etuple(List.map exp e_list)
    | Eapp(Eop(f), e_list) 
	when Types.is_a_hybrid_node f && is_compiled_with_period f ->
        compiled_with_period_error loc f
    | Eapp(op, e_list) ->
        Eapp(op, List.map exp e_list)
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
    | Eperiod _ | Epresent _ | Ematch _ -> assert false in
  { e with e_desc = desc }

and equation (eq_list, env) ({ eq_desc = desc; eq_loc } as eq) =
  match desc with
    | EQeq(({ p_desc = Evarpat(n) } as pat), { e_desc = Eperiod p }) -> 
        let e, eq_list, env = period env eq_list n p in
        { eq with eq_desc = EQeq(pat, e) } :: eq_list, env
    | EQeq(p, ({ e_desc = Eapp(Eop(f), _) })) 
        when Types.is_a_hybrid_node f && is_compiled_with_period f ->
          compiled_with_period_error eq_loc f
    | EQeq _ | EQinit _ | EQnext _ | EQder _ -> eq :: eq_list, env
    | EQmatch(total, e, p_h_list) ->
        let p_h_list =
          List.map 
            (fun ({ m_body = b } as p_h) -> { p_h with m_body = block b }) 
            p_h_list in
        { eq with eq_desc = EQmatch(total, exp e, p_h_list) } :: eq_list, env
    | EQreset(b, e) -> 
      { eq with eq_desc = EQreset(block b, exp e) } :: eq_list, env
    | EQpresent(p_h_list, b_opt) ->
        let p_h_list =
          List.map 
            (fun ({ p_cond = sc; p_body = b } as p_h) -> 
              { p_h with p_cond = scondpat sc; p_body = block b }) 
            p_h_list in
        let b_opt = Misc.optional_map block b_opt in
        { eq with eq_desc = EQpresent(p_h_list, b_opt) } :: eq_list, env
    | EQemit(x, e_opt) ->
        { eq with eq_desc = EQemit(x, Misc.optional_map exp e_opt) } :: eq_list, env
    | EQautomaton _ -> assert false

and scondpat ({ desc = desc } as sc) =
  match desc with
    | Econdand(sc1, sc2) -> 
        { sc with desc = Econdand(scondpat sc1, scondpat sc2) }
    | Econdor(sc1, sc2) -> 
        { sc with desc = Econdor(scondpat sc1, scondpat sc2) }
    | Econdexp(e) -> { sc with desc = Econdexp(exp e) }
    | Econdon(sc1, e) -> 
        { sc with desc = Econdon(scondpat sc1, exp e) }
    | Econdpat(e, pat) -> { sc with desc = Econdpat(exp e, pat) }

and equation_list eq_list = List.fold_left equation ([], Env.empty) eq_list

and block ({ b_vars = n_list; b_body = eq_list; b_env = n_env } as b) =
  (* add local declarations [local x1 in ... in local xn in ...] *)
  let add_locals env n_list n_env =
    let add x entry (n_list, n_env) = x :: n_list, Env.add x entry n_env in
    Env.fold add env (n_list, n_env) in
  
  let eq_list, env = equation_list eq_list in
  let n_list, n_env = add_locals env n_list n_env in
  { b with b_vars = n_list; b_body = eq_list; b_env = n_env }

and local ({ l_eq = eq_list; l_env = l_env } as l) =
  let eq_list, env = equation_list eq_list in
  { l with l_eq = eq_list; l_env = Env.append env l_env }

let clear_period_flag f =
  Global.set_period_desc (Modules.find_value (Lident.Name(f))) (Some false)

let implementation impl =
  match impl.desc with
      | Efundecl(n, ({ f_kind = C; f_body = e } as body)) ->
          clear_period_flag n;
          { impl with desc = Efundecl(n, { body with f_body = exp e }) }
      | Eopen _ | Etypedecl _ | Econstdecl _ | Efundecl _ -> impl

let implementation_list impl_list = Misc.iter implementation impl_list
