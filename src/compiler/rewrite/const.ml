(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2025 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* compile-time evaluation of constant expressions *)
(* those expressions are marked with the keyword "const", e.g. *)
(* let const f = ... and ... in ... *)
(* let rec f<<n>> = ... in ... *)
(* after this step, there should be no more definition of compile-time *)
(* constant values *)
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

(* Invariant: defined names in [e_renaming] and [e_values] must be distinct. *)
type ('info, 'ienv, 'value) env =
  { (* environment for renaming. All variables will be renamed *)
    env_renaming: Ident.t Ident.Env.t;
    (* environment of constant values *)
    env_values: 'value Ident.Env.t;
    (* the global environment of constant values *)
    env_gvalues: 'value Genv.genv;
    (* global definitions of constant values introduced during the reduction *)
    (* the head of the list is the last added value *)
    env_defs: ('info, 'ienv) Zelus.implementation list;
    (* when [x] denotes a constant value [v], [v] has to be turned into *)
    (* an expression. [e_exp] memoize the expression that represents [v] *)
    env_exp: ('info, 'ienv) Zelus.exp Ident.Env.t;
    }

(* All compile-time constant expressions are reduced. A global name *)
(* is introduced to store the value of a constant data-structure *)
(* when this value is used in a non constant expression *)

(* add a global definition [let id = e; [name, id]] *)
let impl name id e = 
  let leq id e = 
    { l_rec = false; l_kind = Kstatic; l_eq = Aux.id_eq id e; 
      l_loc = Location.no_location; l_env = Env.singleton id Typinfo.no_ienv }
  in
  { desc = Eletdecl { d_names = [name, id]; d_leq = leq id e };
    loc = e.e_loc }

let empty =
  { env_renaming = Ident.Env.empty;
    env_values = Ident.Env.empty;
    env_gvalues = Genv.empty;
    env_defs = [];
    env_exp = Ident.Env.empty;
  }

let fresh () = Ident.fresh "const"

let update acc genv env =
  { acc with env_renaming = Ident.Env.empty;
             env_values = env; e_gvalues = genv }

(* Build a renaming from an environment *)
let build ({ env_renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, e_renaming = Env.fold buildrec env (Env.empty, env_renaming) in
  env, { acc with env_renaming }

let error { kind; loc } =
  Format.eprintf "Error during compile-time evaluation of constants\n";
  Error.message loc kind;
  raise Error

let catch v = match v with | Ok(v) -> v | Error(v) -> error v

let pvalue loc c_env =
  let add acc (x, { Value.cur = v }) =
    let* v = v |> Opt.to_result ~none: { Error.kind = Eunbound_ident(x); loc }
    in
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

let var_ident gfuns ({ env_renaming } as acc) x =
  try Env.find x env_renaming, acc
  with Not_found ->
    Format.eprintf 
      "Error during compile-time evaluation of constants; unbound identifier %s"
      (Ident.name x);
    raise Error

(* 
  let rename_t ({ e_renaming } as acc) x = 
  try Env.find x e_renaming, acc
  with Not_found ->
    Format.eprintf 
      "Error during compile-time evaluation of constants; unbound identifier %s"
      (Ident.name x);
    raise Error *)

(* let write_t acc { dv; di; der } =
  let rename acc x = let x, _ = rename_t acc x in x in
  let dv = S.map (rename acc) dv in
  let di = S.map (rename acc) di in
  let der = S.map (rename acc) der in
  { dv; di; der }, acc *)

(* constant evaluation of size expressions *)
let size_e { env_values } si =
  catch (Coiteration.size (Match.liftv env_values) si)

(* Expressions *)
let expression funs acc ({ e_desc; e_loc } as e) =
  match e_desc with
  | Evar(x) ->
     (* If [x] has a constant value [v], that is, it is defined by *)
     (* a [let const x = ...] then [x] is replaced by this value *)
     if Env.mem x acc.env_exp then Env.find x acc.env_exp, acc
     else
       (* or not; then generate a declaration to compute it *)
       if Env.mem x acc.e_values then
         let v = Env.find x acc.e_values in
         let e, acc = value_t e_loc acc v in
         e, { acc with e_exp = Env.add x e acc.e_exp }
       else
         (* otherwise, [x] is not constant; it is renamed *)
         let x, acc = rename_t acc x in
         { e with e_desc = Evar(x) }, acc
  | Eapp ({ is_inline; f; arg_list } as a) ->
     (* if an application need to be inlined *)
     (* it must be a compile-time constant expression *)
     let arg_list, acc =
       Util.mapfold (Mapfold.expression_it funs) acc arg_list in
     let f, acc =
       Mapfold.expression_it funs acc f in
     let f, acc = 
       if is_inline then let v = expression_e acc f in gvalue_t f.e_loc acc f v
       else expression acc f in
     { e with e_desc = Eapp { a with f; arg_list } }, acc
  | Elet(l, e_let) ->
     let l_opt, acc = leq_t acc l in
     let e_let, acc = expression acc e_let in
     { e with e_desc = Aux.opt_letdesc l_opt e_let }, acc
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
  | Esizeapp { f; size_list } -> 
     (* after this step, there should be no static expressions left *)
     let v = expression_e acc f in
     let v_list = List.map (size_e acc) size_list in
     let v = Coiteration.sizeapply e_loc v v_list in
     let v = catch v in
     value_t e_loc acc v
  | _ -> raise Mapfold.Fallback
  

(* Evaluation of an expression *)
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
  match eq_desc with
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
  | EQlet(leq, eq) ->
     let leq_opt, acc = leq_t acc leq in
     let eq, acc = equation acc eq in
     { eq with eq_desc = Aux.opt_eq_letdesc leq_opt eq }, acc
  | EQsizefun _ ->
     error { Error.kind = Eshould_be_static; loc = eq_loc } in
    { eq with eq_write }, acc
  | _ -> raise Mapfold.Fallback

and slet acc leq_list = Util.mapfold_opt leq_t acc leq_list

(* eval a definition *)
and leq_e acc leq =
  let l_env =
    Coiteration.vleq acc.e_gvalues (Match.liftv acc.e_values) leq in
  catch l_env

(* evaluation of compile-time definitions *)
and const_leq_t acc leq =
  let l_env = leq_e acc leq in
  (* let l = Env.to_list l_env in *)
  None, { acc with e_values = Env.append l_env acc.e_values }

and leq_t acc ({ l_kind; l_eq; l_env; l_loc } as leq) =
  match l_kind with
  | Kconst ->
     (* evaluation of compile-time expressions *)
     const_leq_t acc leq
  | Kstatic | Kany -> 
     (* equations are not evaluated *)
     let l_env, acc = build acc l_env in
     let l_eq, acc = equation acc l_eq in
     Some { leq with l_eq; l_env }, acc

                
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
         { acc with e_defs =
                      impl name m (Aux.emake (Efun(f))) :: acc_local.e_defs }
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

let letdecl_list loc acc d_leq_opt d_names =
  let add_gvalue ({ e_values; e_gvalues } as acc) (name, id) =
    try
      let v = Env.find id e_values in
      { acc with e_gvalues = Genv.add name v e_gvalues }
    with
    | Not_found -> acc in
  match d_leq_opt with
  | None ->
     (* all names define compile-time constant values *)
     (* no code is generated but the global environment is updated *)
     List.fold_left add_gvalue acc d_names
  | Some(d_leq) ->
     let d_names =
       List.map
         (fun (name, id) -> let id, _ = rename_t acc id in name, id) d_names in
     { acc with e_defs =
                  { desc = Eletdecl { d_leq; d_names }; loc } :: acc.e_defs }

(* an equation is immediate if it defines values which do not need any *)
(* computation to be done *)
let immediate { l_eq } =
  let rec equation { eq_desc } =
    match eq_desc with
    | EQsizefun _ -> true
    | EQeq(p, e) -> expression e
    | EQand { eq_list } -> List.for_all equation eq_list
    | _ -> false
  and expression { e_desc } =
    match e_desc with
    | Econst _ | Efun _ -> true | _ -> false in
  equation l_eq

(* The main function. Reduce every definition *)
let implementation acc ({ desc; loc } as impl) =
  match desc with
  | Eopen(name) ->
     (* add [name] in the list of known modules *)
     (* load it if it exists *)
     (* This is a temporary solution: it uses two distinct tables *)
     (* one for storing type informations; one for storing values. I *)
     (* should take the solution used version 2, with a unique table *)
     { acc with e_gvalues = Genv.try_to_open_module acc.e_gvalues name;
                e_defs = impl :: acc.e_defs }
  | Eletdecl { d_names; d_leq } ->
     (* [d_leq] must be either constant or static *)
     let d_leq_opt, acc = leq_t acc d_leq in
     letdecl_list loc acc d_leq_opt d_names
  | Etypedecl _ -> { acc with e_defs = impl :: acc.e_defs }

let set_index_t n = Ident.set n
let get_index_t () = Ident.get ()

let program otc genv { p_impl_list; p_index } =
  set_index_t p_index;
  let { e_gvalues; e_defs } =
    List.fold_left implementation { empty with e_gvalues = genv } p_impl_list in
  apply_with_close_out (Genv.write e_gvalues) otc;
  (* definitions in [acc.e_defs] are in reverse order *)
  let p_impl_list = List.rev e_defs in
  let p_index = get_index_t () in
  { p_impl_list; p_index }

