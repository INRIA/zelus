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

(** reduce static expressions *)

open Misc
open Location
open Ident
open Lident
open Zelus
open Monad
open Opt
open Result
open Defnames
open Error

(* Invariant: defined names in [e_renaming] and [e_values] *)
(* are pairwise distinct. For that, all defined names in the source *)
(* must be pairwise distinct *)
type ('info, 'ienv, 'value) env =
  { e_renaming: Ident.t Ident.Env.t; (* environment for renaming *)
    e_values: 'value Ident.Env.t;  (* environment of static values *)
    e_gvalues: 'value Genv.genv;
    (* global environment of static values *)
    e_defs: ('info, 'ienv) Zelus.implementation list;
    (* global definitions of static values introduced during the reduction *)
    (* the head of the list is the last added value *)
    e_exp: ('info, 'ienv) Zelus.exp Ident.Env.t;
    (* the expression associated to [x] *)
    (* when [x] is a static value *)
  }

(* All static expressions are reduced. Static expressions bound to variables *)
(* that are later used in a non static expression are introduced as global *)
(* declarations *)

(* add global definitions in the list of global declarations of the module *)
let leq id e = 
  { l_rec = false; l_kind = Kstatic; l_eq = Aux.id_eq id e; 
    l_loc = Location.no_location; l_env = Env.singleton id Typinfo.no_ienv }
let impl name id e = 
    { desc = Eletdecl { d_names = [name, id]; d_leq = leq id e };
      loc = e.e_loc }
    
let empty =
  { e_renaming = Ident.Env.empty;
    e_values = Ident.Env.empty;
    e_gvalues = Genv.empty;
    e_defs = [];
    e_exp = Ident.Env.empty;
  }

let fresh () = Ident.fresh "r"

let update acc genv env =
  { acc with e_renaming = Ident.Env.empty; e_values = env; e_gvalues = genv }

(** Build a renaming from an environment *)
let build ({ e_renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, e_renaming = Env.fold buildrec env (Env.empty, e_renaming) in
  env, { acc with e_renaming }

let error { kind; loc } =
  Format.eprintf "Error during static reduction\n";
  Error.message loc kind;
  raise Error

let catch v = match v with | Ok(v) -> v | Error(v) -> error v

let pvalue loc c_env =
  let add acc (x, { Value.cur = v }) =
    let* v = v |> Opt.to_result ~none: { Error.kind = Eunbound_ident(x); loc } in
    let* v = Primitives.pvalue v |>
               Opt.to_result ~none: { Error.kind = Etype; loc } in
    return (Env.add x v acc) in
  let c_env = Env.to_seq c_env in
  let c_env = seqfold add Env.empty c_env in
  catch c_env

let no_leq loc =
  { l_loc = loc; l_kind = Kstatic;l_rec = false;
    l_eq = { eq_desc = EQempty; eq_write = Defnames.empty;
             eq_loc = loc; eq_index = -1; eq_safe = true }; 
    l_env = Ident.Env.empty }

let rename_t ({ e_renaming } as acc) x = 
  try Env.find x e_renaming, acc
  with Not_found ->
    Debug.print_string "Static: unbound identifier" (Ident.name x);
    raise Error (* x, acc *)

let write_t acc { dv; di; der } =
  let rename acc x = let x, _ = rename_t acc x in x in
  let dv = S.map (rename acc) dv in
  let di = S.map (rename acc) di in
  let der = S.map (rename acc) der in
  { dv; di; der }, acc

let type_expression acc ty = ty, acc

(* static evaluation of size expressions *)
let size_e { e_values } si =
  catch (Coiteration.size (Match.liftv e_values) si)

(** Renaming of patterns *)
let rec pattern f acc ({ pat_desc } as p) =
  let pat_desc, acc = match pat_desc with
    | Ewildpat | Econstpat _ | Econstr0pat _ -> pat_desc, acc
    | Evarpat(v) ->
       let v, acc = f acc v in
       Evarpat(v), acc
    | Etuplepat(p_list) ->
       let p_list, acc = Util.mapfold (pattern f) acc p_list in
       Etuplepat(p_list), acc
    | Econstr1pat(c, p_list) ->
       let p_list, acc = Util.mapfold (pattern f) acc p_list in
       Econstr1pat(c, p_list), acc
    | Erecordpat(n_p_list) ->
       let n_p_list, acc =
         Util.mapfold 
           (fun acc { label; arg } ->
             let arg, acc = pattern f acc p in
             { label; arg}, acc) acc n_p_list in
       Erecordpat(n_p_list), acc
    | Ealiaspat(p1, n) ->
       let p1, acc = pattern f acc p1 in
       let n, acc = f acc n in
       Ealiaspat(p1, n), acc
    | Eorpat(p1, p2) ->
       let p1, acc = pattern f acc p1 in
       let p2, acc = pattern f acc p2 in
       Eorpat(p1, p2), acc
    | Etypeconstraintpat(p1, ty) ->
       let p1, acc = pattern f acc p1 in
       let ty, acc = type_expression acc ty in
       Etypeconstraintpat(p1, ty), acc in
  { p with pat_desc }, acc

let pattern acc p = pattern rename_t acc p

let default_t f acc d =
  match d with
  | Init(e) -> let e, acc = f acc e in Init(e), acc
  | Else(e) -> let e, acc = f acc e in Else(e), acc
  | NoDefault -> NoDefault, acc

let for_exit_t expression acc ({ for_exit } as fe) =
  let for_exit, acc = expression acc for_exit in
  { fe with for_exit }, acc

let for_kind_t expression acc for_kind =
  match for_kind with
  | Kforeach -> Kforeach, acc
  | Kforward(for_exit_opt) ->
     let for_exit_opt, acc = 
       Util.optional_with_map (for_exit_t expression) acc for_exit_opt in
     Kforward(for_exit_opt), acc
    
let for_size_t expression acc e = expression acc e

let for_input_t expression acc ({ desc } as fi) =
  let desc, acc = match desc with
    | Einput {id; e; by } ->
       let id, acc = rename_t acc id in
       let e, acc = expression acc e in
       let by, acc = Util.optional_with_map expression acc by in
       Einput { id; e; by }, acc
    | Eindex ({ id; e_left; e_right } as ind) ->
       let id, acc = rename_t acc id in
       let e_left, acc = expression acc e_left in
       let e_right, acc = expression acc e_right in
       Eindex { ind with id; e_left; e_right }, acc in
  { fi with desc }, acc
     
(** Expressions **)
let rec expression acc ({ e_desc; e_loc } as e) =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> e, acc
  | Evar(x) ->
     (* If [x] has a static value, [x] is replaced by this value *)
     (* either there exist a global definition for x *)
     if Env.mem x acc.e_exp then Env.find x acc.e_exp, acc
     else
       (* or not; then generate a declaration to compute it *)
       if Env.mem x acc.e_values then
         let v = Env.find x acc.e_values in
         let e, acc = value_t e_loc acc v in
         e, { acc with e_exp = Env.add x e acc.e_exp }
       else
         (* otherwise, [x] is not static; it is renamed *)
         let x, acc = rename_t acc x in
         { e with e_desc = Evar(x) }, acc
  | Elast({ id } as l) ->
     let id, acc = rename_t acc id in
     { e with e_desc = Elast({ l with id }) }, acc
  | Etuple(e_list) ->
     let e_list, acc = Util.mapfold expression acc e_list in
     { e with e_desc = Etuple(e_list) }, acc
  | Econstr1 { lname; arg_list } ->
     let arg_list, acc = Util.mapfold expression acc arg_list in
     { e with e_desc = Econstr1 { lname; arg_list } }, acc
  | Erecord(l_e_list) -> 
      let l_e_list, acc =
        Util.mapfold (fun acc { label; arg } ->
            let arg, acc = expression acc arg in 
            { label; arg }, acc) acc l_e_list in
      { e with e_desc = Erecord(l_e_list) }, acc
  | Erecord_access { label; arg } ->
      let arg, acc = expression acc arg in
      { e with e_desc = Erecord_access { label; arg } }, acc
  | Erecord_with(e_record, l_e_list) -> 
     let e_record, acc = expression acc e_record in
     let l_e_list, acc =
       Util.mapfold
	  (fun acc { label; arg } ->
            let arg, acc = expression acc e in { label; arg }, acc)
          acc l_e_list in
      { e with e_desc = Erecord_with(e_record, l_e_list) }, acc
  | Eapp ({ is_inline; f; arg_list } as a) ->
     (* if an application need to be inlined *)
     (* it must be a static expression *)
     let arg_list, acc = Util.mapfold expression acc arg_list in
     let f, acc = 
       if is_inline then let v = expression_e acc f in gvalue_t f.e_loc acc f v
       else expression acc f in
     { e with e_desc = Eapp { a with f; arg_list } }, acc
  | Eop(op, e_list) ->
     let e_list, acc = Util.mapfold expression acc e_list in
     { e with e_desc = Eop(op, e_list) }, acc
  | Etypeconstraint(e_ty, ty) ->
     let e_ty, acc = expression acc e_ty in
     { e with e_desc = Etypeconstraint(e_ty, ty) }, acc
  | Elet(l, e_let) ->
     let l, acc = leq_t acc l in
     let e_let, acc = expression acc e_let in
     { e with e_desc = Elet(l, e_let) }, acc
  | Elocal(eq_b, e) ->
     let eq_b, acc = block acc eq_b in
     let e, acc = expression acc e in
     { e with e_desc = Elocal(eq_b, e) }, acc
  | Epresent({ handlers; default_opt }) ->
     let body acc ({ p_cond; p_body; p_env } as p_b) =
       let p_env, acc = build acc p_env in
       let p_cond, acc = scondpat acc p_cond in
       let p_body, acc = expression acc p_body in
       { p_b with p_cond; p_body; p_env }, acc in
     let handlers, acc =
       Util.mapfold body acc handlers in
     let default_opt, acc = default_t expression acc default_opt in
     { e with e_desc = Epresent { handlers; default_opt } }, acc 
  | Ematch({ e; handlers } as m) ->
     let body acc ({ m_pat; m_body; m_env } as m_h) =
       let m_env, acc = build acc m_env in
       let m_pat, acc = pattern acc m_pat in
       let m_body, acc = expression acc m_body in
       { m_h with m_pat; m_body; m_env }, acc in
     (* two cases; either [e] is compile-time or not *)
     let v = try_expression acc e in
     let e, acc = match v with
       | None ->
          let e, acc = expression acc e in
          let handlers, acc =
            Util.mapfold body acc handlers in
          { e with e_desc = Ematch { m with e; handlers } }, acc
       | Some(v) ->
          let env_pat, e = 
            catch (Match.select e_loc acc.e_gvalues acc.e_values v handlers)
          in expression 
               { acc with e_values = Env.append env_pat acc.e_values } e in
       e, acc
  | Eassert e -> let e, acc = expression acc e in
                 { e with e_desc = Eassert(e) }, acc
  | Ereset(e_body, e_c) ->
     let e_body, acc = expression acc e_body in
     let e_c, acc = expression acc e_c in
     { e with e_desc = Ereset(e_body, e_c) }, acc
  | Esizeapp { f; size_list } -> 
     (* after this step, there should be no static expressions left *)
     let v = expression_e acc f in
     let v_list = List.map (size_e acc) size_list in
     let v = Coiteration.sizeapply e_loc v v_list in
     let v = catch v in
     value_t e_loc acc v
  | Efun f ->
     let f, acc = funexp acc f in
     { e with e_desc = Efun f }, acc
  | Eforloop
     ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
     let for_vardec_t acc ({ desc = { for_array; for_vardec } } as f) =
       let for_vardec, acc = vardec acc for_vardec in
       { f with desc = { for_array; for_vardec } }, acc in
     let for_index_t acc id = rename_t acc id in
     let for_exp_t acc for_exp =
       match for_exp with
       | Forexp { exp; default } ->
          let exp, acc = expression acc exp in
          let default, acc = Util.optional_with_map expression acc default in
          Forexp { exp; default }, acc
       | Forreturns { r_returns; r_block; r_env } ->
          let r_env, acc = build acc r_env in
          let r_returns, acc = Util.mapfold for_vardec_t acc r_returns in
          let r_block, acc = block acc r_block in
          Forreturns { r_returns; r_block; r_env }, acc in
     let for_env, acc = build acc for_env in
     let for_index, acc = Util.optional_with_map for_index_t acc for_index in
     let for_size, acc =
       Util.optional_with_map (for_size_t expression) acc for_size in
     let for_input, acc =
       Util.mapfold (for_input_t expression) acc for_input in
     let for_body, acc = for_exp_t acc for_body in
     let for_kind, acc = for_kind_t expression acc for_kind in
     { e with e_desc =
                Eforloop
                  { f with for_size; for_kind; for_index; for_input;
                           for_body; for_env } }, acc

and funexp acc ({ f_args; f_body; f_env } as f) =
  let f_env, acc_local = build acc f_env in
  let arg acc v_list = Util.mapfold vardec acc v_list in
  let f_args, acc_local = Util.mapfold arg acc_local f_args in
  let f_body, acc_local = result acc_local f_body in
  { f with f_args; f_body; f_env }, { acc with e_defs = acc_local.e_defs }

(** Evaluation of an expression *)
and expression_e acc e =
  let v = Coiteration.vexp acc.e_gvalues (Match.liftv acc.e_values) e in
  catch v

(** Try to evaluate an expression; expect the result to be a boolean *)
and try_expression_bool acc e =
  let env = Match.liftv acc.e_values in
  let v = 
    Coiteration.try_vexp_into_bool acc.e_gvalues env e in
  Result.to_option v

and try_expression acc e =
  let env = Match.liftv acc.e_values in
  catch(Coiteration.try_vexp acc.e_gvalues env e)

(** Equations **)
and equation acc ({ eq_desc; eq_write; eq_loc } as eq) = 
  let eq_write, acc = write_t acc eq_write in
  let eq, acc = match eq_desc with
    | EQeq(p, e) ->
       let p, acc = pattern acc p in
       let e, acc = expression acc e in
       { eq with eq_desc = EQeq(p, e) }, acc
    | EQinit(x, e) ->
       let e, acc = expression acc e in
       let x, acc = rename_t acc x in
       { eq with eq_desc = EQinit(x, e) }, acc
    | EQemit(x, e_opt) ->
       let x, acc = rename_t acc x in
       let e_opt, acc =
         Util.optional_with_map expression acc e_opt in
       { eq with eq_desc = EQemit(x, e_opt) }, acc
    | EQder { id; e; e_opt; handlers } ->
       let body acc ({ p_cond; p_body; p_env } as p_b) =
         let p_env, acc = build acc p_env in
         let p_cond, acc = scondpat acc p_cond in
         let p_body, acc = expression acc p_body in
         { p_b with p_cond; p_body }, acc in
       let id, acc = rename_t acc id in
       let e, acc = expression acc e in
       let e_opt, acc = Util.optional_with_map expression acc e_opt in
       let handlers, acc = Util.mapfold body acc handlers in
       { eq with eq_desc = EQder { id; e; e_opt; handlers } }, acc
    | EQif { e; eq_true; eq_false } ->
       (* two cases; either [e] is a compile-time or not *)
       let v = try_expression_bool acc e in
       let eq, acc = match v with 
         | None -> let e, ac = expression acc e in
                   let eq_true, acc = equation acc eq_true in
                   let eq_false, acc = equation acc eq_false in
                   { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
         | Some(b) ->
            if b then equation acc eq_true else equation acc eq_false in
       eq, acc
    | EQmatch({ e; handlers } as m) ->
       let body acc ({ m_pat; m_body; m_env } as m_h) =
         let m_env, acc = build acc m_env in
         let m_pat, acc = pattern acc m_pat in
         let m_body, acc = equation acc m_body in
         { m_h with m_pat; m_body; m_env }, acc in
       (* two cases; either [e] is compile-time or not *)
       let v = try_expression acc e in
       let eq, acc = match v with
         | None ->
            let e, acc = expression acc e in
            let handlers, acc =
              Util.mapfold body acc handlers in
            { eq with eq_desc = EQmatch { m with e; handlers } }, acc
         | Some(v) ->
            let env_pat, eq = 
              catch (Match.select eq_loc acc.e_gvalues acc.e_values v handlers)
            in equation 
                 { acc with e_values = Env.append env_pat acc.e_values } eq in
       eq, acc
    | EQlocal(eq_b) ->
       let eq_b, acc = block acc eq_b in
       { eq with eq_desc = EQlocal(eq_b) }, acc
    | EQand({ eq_list } as a) ->
       let eq_list, acc = Util.mapfold equation acc eq_list in
       { eq with eq_desc = EQand { a with eq_list } }, acc
    | EQpresent({ handlers; default_opt }) ->
       let body acc ({ p_cond; p_body; p_env } as p_b) =
         let p_env, acc = build acc p_env in
         let p_cond, acc = scondpat acc p_cond in
         let p_body, acc = equation acc p_body in
         { p_b with p_cond; p_body }, acc in
       let handlers, acc =
         Util.mapfold body acc handlers in
       let default_opt, acc = default_t equation acc default_opt in
       { eq with eq_desc = EQpresent { handlers; default_opt } }, acc
    | EQautomaton({ handlers; state_opt } as a) ->
       let statepat acc ({ desc } as spat) =
         let desc, acc = match desc with
           | Estate0pat(id) ->
              let id, acc = rename_t acc id in
            Estate0pat(id), acc
         | Estate1pat(id, id_list) ->
            let id, ac = rename_t acc id in
            let id_list, acc = Util.mapfold rename_t acc id_list in
            Estate1pat(id, id_list), acc in
         { spat with desc }, acc in
       let rec state acc ({ desc } as st) =
         let desc, acc  = match desc with
           | Estate0(id) ->
              let id, acc = rename_t acc id in
              Estate0(id), acc
           | Estate1(id, e_list) ->
              let id, acc = rename_t acc id in
              let e_list, acc = Util.mapfold expression acc e_list in
              Estate1(id, e_list), acc
           | Estateif(e, st1, st2) ->
              let e, acc = expression acc e in
              let st1, acc = state acc st1 in
              let st2, acc = state acc st2 in
              Estateif(e, st1, st2), acc in
         { st with desc }, acc in
       let escape acc ({ e_cond; e_let; e_body; e_next_state; e_env } as esc) =
         let e_env, acc = build acc e_env in
         let e_cond, acc = scondpat acc e_cond in
         let e_let, acc = slet acc e_let in
         let e_body, acc = block acc e_body in
         let e_next_state, acc = state acc e_next_state in
         { esc with e_cond; e_let; e_body; e_next_state; e_env }, acc in
       let handler acc ({ s_state; s_let; s_body; s_trans } as h) =
         let s_state, acc = statepat acc s_state in
         let s_let, acc = slet acc s_let in
         let s_body, acc = block acc s_body in
         let s_trans, acc = Util.mapfold escape acc s_trans in
         { h with s_state; s_let; s_body; s_trans }, acc in
       let state_opt, acc = Util.optional_with_map state acc state_opt in
       let handlers, acc = Util.mapfold handler acc handlers in
       { eq with eq_desc = EQautomaton({ a with handlers; state_opt }) }, acc
    | EQempty -> eq, acc
    | EQassert(e) ->
       let e, acc = expression acc e in
       { eq with eq_desc = EQassert(e) }, acc
    | EQforloop
       ({ for_size; for_kind; for_index; for_input; for_body; for_env } as f) ->
       let for_index_t acc id = rename_t acc id in
       let for_eq_t acc { for_out; for_block; for_out_env } =
         let for_out_t acc
               ({ desc = { for_name; for_out_name; for_init; for_default } } as f) =
           let for_name, acc = rename_t acc for_name in
           let for_out_name, acc = 
             Util.optional_with_map rename_t acc for_out_name in
           let for_init, acc = Util.optional_with_map expression acc for_init in
           let for_default, acc =
             Util.optional_with_map expression acc for_default in
           { f with desc = { for_name; for_out_name; for_init; for_default } },
           acc in
         let for_out_env, acc = build acc for_out_env in
         let for_out, acc =
           Util.mapfold for_out_t acc for_out in
         let for_block, acc = block acc for_block in
         { for_out; for_block; for_out_env }, acc in
       let for_env, acc = build acc for_env in
       let for_index, acc = Util.optional_with_map for_index_t acc for_index in
       let for_size, acc =
         Util.optional_with_map (for_size_t expression) acc for_size in
       let for_input, acc =
         Util.mapfold (for_input_t expression) acc for_input in
       let for_body, acc = for_eq_t acc for_body in
       let for_kind, acc = for_kind_t expression acc for_kind in
       { eq with eq_desc =
                   EQforloop
                     { f with for_size; for_kind; for_index; for_input;
                              for_body; for_env } }, acc
    | EQreset(eq, e_c) ->
       let eq, acc = equation acc eq in
       let e_c, acc = expression acc e_c in
       { eq with eq_desc = EQreset(eq, e_c) }, acc
    | EQlet(leq, eq) ->
       let leq, acc = leq_t acc leq in
       let eq, acc = equation acc eq in
       { eq with eq_desc = EQlet(leq, eq) }, acc
    | EQsizefun _ ->
       error { Error.kind = Eshould_be_static; loc = eq_loc } in
  { eq with eq_write }, acc

and slet acc leq_list = Util.mapfold leq_t acc leq_list

(* eval a definition *)
and leq_e acc leq =
  let l_env =
    Coiteration.vleq acc.e_gvalues (Match.liftv acc.e_values) leq in
  catch l_env

and leq_t acc ({ l_kind; l_eq; l_env; l_loc } as leq) =
  match l_kind with
  | Kconst | Kstatic ->
     (* static evaluation *)
     let l_env = leq_e acc leq in
     (* let l = Env.to_list l_env in *)
     no_leq l_loc, { acc with e_values = Env.append l_env acc.e_values }
  | Kany -> 
     let l_env, acc = build acc l_env in
     let l_eq, acc = equation acc l_eq in
     { leq with l_eq; l_env }, acc

and scondpat acc ({ desc = desc } as scpat) =
  match desc with
  | Econdand(scpat1, scpat2) ->
     let scpat1, acc = scondpat acc scpat1 in
     let scpat2, acc = scondpat acc scpat2 in
     { scpat with desc = Econdand(scpat1, scpat2) }, acc
  | Econdor(scpat1, scpat2) ->
     let scpat1, acc = scondpat acc scpat1 in
     let scpat2, acc = scondpat acc scpat2 in
     { scpat with desc = Econdor(scpat1, scpat2) }, acc
  | Econdexp(e) ->
     let e, acc = expression acc e in
     { scpat with desc = Econdexp(e) }, acc
  | Econdpat(e, p) ->
     let e, acc = expression acc e in
     let p, acc = pattern acc p in
     { scpat with desc = Econdpat(e, p) }, acc
  | Econdon(scpat, e) ->
     let scpat, acc = scondpat acc scpat in
     let e, acc = expression acc e in
     { scpat with desc = Econdon(scpat, e) }, acc

and vardec acc ({ var_name; var_default; var_init; var_typeconstraint } as v) =
  let var_name, acc = rename_t acc var_name in
  let var_default, acc =
    Util.optional_with_map expression acc var_default in
  let var_init, acc = Util.optional_with_map expression acc var_init in
  let var_typeconstraint, acc =
    Util.optional_with_map type_expression acc var_typeconstraint in
  { v with var_name; var_default; var_init; var_typeconstraint }, acc

                 
and block acc ({ b_vars; b_body; b_env; b_write } as b) =
  let b_env, acc = build acc b_env in
  let b_vars, acc = 
    Util.mapfold vardec acc b_vars in
  let b_body, acc = equation acc b_body in
  let b_write, acc = write_t acc b_write in
  { b with b_vars; b_body; b_env; b_write }, acc

and result acc ({ r_desc } as r) =
  let r_desc, acc = match r_desc with
    | Exp(e) -> let e, acc = expression acc e in Exp(e), acc
    | Returns(b_eq) -> let b_eq, acc = block acc b_eq in Returns(b_eq), acc in
  { r with r_desc }, acc

and immediate { e_desc } =
  match e_desc with 
  | Econst _ | Econstr0 _ | Eglobal _ -> true | _ -> false

(* translate a static value - introduce global definitions for functions *)
and value_t loc acc v =
  let unexpected_failure s =
    catch (error { kind = Error.Eunexpected_failure
                            { arg = s;
                              print = fun ff s -> Format.fprintf ff "%s" s };
                   loc = no_location }) in
  let rec value_t acc v =
    let open Value in
    let e_desc, acc = match v with
      | Vint(v) -> Econst(Eint(v)), acc
      | Vbool(v) -> Econst(Ebool(v)), acc
      | Vfloat(v) -> Econst(Efloat(v)), acc
      | Vchar(v) -> Econst(Echar(v)), acc
      | Vstring(v) -> Econst(Estring(v)), acc
      | Vvoid -> Econst(Evoid), acc
      | Vconstr0 lname -> Econstr0 { lname }, acc
      | Vconstr1(lname, v_list) ->
         let arg_list, acc = Util.mapfold value_t acc v_list in
         Econstr1 { lname; arg_list }, acc
      | Vrecord(r_list) ->
         let e_list, acc =
           Util.mapfold
             (fun acc { label; arg } -> let arg, acc = value_t acc arg in 
                                        { label; arg}, acc) acc r_list in
         Erecord e_list, acc
      | Vstuple(v_list) ->
         let e_list, acc = Util.mapfold value_t acc v_list in
         Etuple e_list, acc
      | Vtuple(v_list) ->
         let value_t acc v =
           let v = 
             catch (Primitives.pvalue v |>
                      Opt.to_result ~none: { Error.kind = Etype; loc }) in
           value_t acc v in
         let e_list, acc = Util.mapfold value_t acc v_list in
         Etuple(e_list), acc
      | Vclosure { c_funexp; c_genv; c_env } ->
         (* Warning: add part of [g_env and c_env] in acc *)
         let c_env = pvalue loc c_env in
         let acc_local = update acc c_genv c_env in
         let f, acc_local = funexp acc_local c_funexp in 
         (* add a definition in the global environment *)
         let m = Ident.fresh "r" in
         let name = Ident.name m in
         Eglobal { lname = Name(Ident.name m) },
         { acc with e_defs = impl name m (Aux.emake (Efun(f))) :: acc_local.e_defs }
      | Varray(a) ->
         let v = catch (Arrays.flat_of_map a) in
         let v, acc = Util.mapfold value_t acc (Array.to_list v) in
         Eop(Earray(Earray_list), v), acc
      (* none of the value below should appear *)
      | Vpresent _ ->
         unexpected_failure "present"
      | Vabsent ->
         unexpected_failure "absent"
      | Vstate0 _ | Vstate1 _ ->
         unexpected_failure "state"
      | Vsizefun _ ->
         unexpected_failure "sizefun"
      | Vsizefix _ ->
         unexpected_failure "sizefix"
      | Vfun _  -> unexpected_failure "vfun" in
    Aux.emake e_desc, acc in
  let e, acc = value_t acc v in
  (* if [e] is not immediate, add a global definition to store it *)
  if immediate e then e, acc
  else 
    (* add a definition in the global environment *)
    let m = fresh () in
    let name = Ident.name m in
    let gname = Aux.emake (Eglobal { lname = Name(name) }) in
    gname, { acc with e_defs = impl name m e :: acc.e_defs;
                      e_gvalues = Genv.add name v acc.e_gvalues }

and gvalue_t loc acc ({ e_desc } as e) v =
  if immediate e then e, acc
  else value_t loc acc v

let letdecl_list loc acc d_names =
  let is_a_sizefun v =
    match v with | Value.Vsizefix _ | Value.Vsizefun _ -> true | _ -> false in
  let letdecl acc (name, id) =
    let v = Env.find id acc.e_values in
    let acc = { acc with e_gvalues = Genv.add name v acc.e_gvalues } in
    if Env.mem id acc.e_exp then
      { acc with e_defs = impl name id (Env.find id acc.e_exp) :: acc.e_defs }
    else
      (* values that are parameterized by static ones like functions *)
      (* sizes are not emitted *)
      if is_a_sizefun v then acc
      else
        let e, acc = value_t loc acc v in
        { acc with e_exp = Env.add id e acc.e_exp;
                   e_defs = impl name id e :: acc.e_defs } in
  List.fold_left letdecl acc d_names
    
(* The main function. Reduce every definition *)
let implementation acc ({ desc; loc } as impl) =
  match desc with
  | Eopen(name) ->
    (* add [name] in the list of known modules *)
    { acc with e_gvalues = Genv.open_module acc.e_gvalues name;
               e_defs = impl :: acc.e_defs }
  | Eletdecl { d_names; d_leq } ->
    (* [d_leq] must be static *)
    let env = leq_e acc d_leq in
    (* for every entry [m, id] in [d_names] *)
    (* add the global declaration [m, e] if [id] is associated to [e] *)
    letdecl_list loc { acc with e_values = Env.append env acc.e_values } d_names
  | Etypedecl _ -> { acc with e_defs = impl :: acc.e_defs }

let set_index_t n = Ident.set n
let get_index_t () = Ident.get ()

let program genv { p_impl_list; p_index } =
  set_index_t p_index;
  let { e_defs } =
    List.fold_left implementation { empty with e_gvalues = genv } p_impl_list in
  (* definitions in [acc.e_defs] are in reverse order *)
  let p_impl_list = List.rev e_defs in
  let p_index = get_index_t () in
  { p_impl_list; p_index }
  
