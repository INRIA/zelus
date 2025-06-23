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
    renaming: Ident.t Ident.Env.t;
    (* environment of constant values *)
    values: 'value Ident.Env.t;
    (* the global environment of constant values *)
    gvalues: 'value Genv.genv;
    (* global definitions of constant values introduced during the reduction *)
    (* the head of the list is the last added value *)
    defs: ('info, 'ienv) Zelus.implementation list;
    (* when [x] denotes a constant value [v], [v] has to be turned into *)
    (* an expression. [exp] memoize the expression that represents [v] *)
    exp: ('info, 'ienv) Zelus.exp Ident.Env.t;
    }

(* All compile-time constant expressions are reduced. A global name *)
(* is introduced to store the value of a constant value *)
(* when this value is used in a non constant expression *)

let empty =
  { renaming = Ident.Env.empty;
    values = Ident.Env.empty;
    gvalues = Genv.empty;
    defs = [];
    exp = Ident.Env.empty;
  }

let fresh () = Ident.fresh "const"

let update_with_no_renaming acc genv env =
  { acc with renaming = Ident.Env.empty; values = env; gvalues = genv }

let error { kind; loc } =
  Format.eprintf "Error during compile-time evaluation of constants\n";
  Error.message loc kind;
  raise Error

let catch v = match v with | Ok(v) -> v | Error(v) -> error v

let pvalue_of_env loc c_env =
  let add acc (x, { Value.cur = v }) =
    let* v = v |> Opt.to_result ~none: { Error.kind = Eunbound_ident(x); loc }
    in
    let* v = Primitives.pvalue v |>
               Opt.to_result ~none: { Error.kind = Etype; loc } in
    return (Env.add x v acc) in
  let c_env = Env.to_seq c_env in
  let c_env = seqfold add Env.empty c_env in
  catch c_env

(* add a global definition [let id = e; [name, id]] *)
let add_global_definition name id e = 
  let leq id e = 
    { l_rec = false; l_kind = Kstatic; l_eq = Aux.id_eq id e; 
      l_loc = Location.no_location; l_env = Env.singleton id Typinfo.no_ienv }
  in
  { desc = Eletdecl { d_names = [name, id]; d_leq = leq id e };
    loc = e.e_loc }

(* Translation of values *)
(* [exp_of_value loc funs acc v] represents [v] as an expression *)
(* it will be defined as a global variable unless it is an immediate value *)
let rec exp_of loc funs acc v =
  let unexpected_failure s =
    catch (error { kind = Error.Eunexpected_failure
                            { arg = s;
                              print = fun ff s -> Format.fprintf ff "%s" s };
                   loc = no_location }) in
  let rec exp_of acc v =
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
         let arg_list, acc = Util.mapfold exp_of acc v_list in
         Econstr1 { lname; arg_list }, acc
      | Vrecord(r_list) ->
         let e_list, acc =
           Util.mapfold
             (fun acc { label; arg } -> let arg, acc = exp_of acc arg in 
                                        { label; arg}, acc) acc r_list in
         Erecord e_list, acc
      | Vstuple(v_list) ->
         let e_list, acc = Util.mapfold exp_of acc v_list in
         Etuple e_list, acc
      | Vtuple(v_list) ->
         let value_t acc v =
           let v = 
             catch (Primitives.pvalue v |>
                      Opt.to_result ~none: { Error.kind = Etype; loc }) in
           exp_of acc v in
         let e_list, acc = Util.mapfold value_t acc v_list in
         Etuple(e_list), acc
      | Vclosure { c_funexp; c_genv; c_env } ->
         (* add part of [g_env] and [c_env] in acc *)
         let c_env = pvalue_of_env loc c_env in
         let acc_local = update_with_no_renaming acc c_genv c_env in
         (* reduce compile-time constants in the body of the function *)
         let f, acc_local = Mapfold.funexp_it funs acc_local c_funexp in 
         (* add a definition [m = fun(f)] in the global environment *)
         let m = fresh () in
         let name = Ident.name m in
         let defs = 
           add_global_definition name m (Aux.emake (Efun(f))) :: acc_local.defs in
         Eglobal { lname = Name(Ident.name m) },
         { acc with defs }
      | Varray(a) ->
         let v = catch (Arrays.flat_of_map a) in
         let v, acc = Util.mapfold exp_of acc (Array.to_list v) in
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
  let e, acc = exp_of acc v in
  (* if [e] is not immediate, add a global definition to store it *)
  if is_immediate e then e, acc
  else 
    (* add a definition in the global environment *)
    let m = fresh () in
    let name = Ident.name m in
    let gname = Aux.emake (Eglobal { lname = Name(name) }) in
    let defs =
      add_global_definition name m e :: acc.defs in
    let gvalues = Genv.add name v acc.gvalues in
    gname, { acc with defs; gvalues }

and is_immediate { e_desc } =
  match e_desc with 
  | Econst _ | Econstr0 _ | Eglobal _ -> true | _ -> false

let gvalue_texp_of_value loc funs acc ({ e_desc } as e) v =
  if is_immediate e then e, acc
  else exp_of loc funs acc v

(* Build a renaming from an environment *)
let build global_funs ({ renaming } as acc) env =
  let buildrec n entry (env, renaming) =
    let m = Ident.fresh (Ident.source n) in
    Env.add m entry env,
    Env.add n m renaming in
  let env, renaming = Env.fold buildrec env (Env.empty, renaming) in
  env, { acc with renaming }

let var_ident global_funs ({ renaming } as acc) x =
  try Env.find x renaming, acc
  with Not_found ->
    Format.eprintf 
      "@[Error during compile-time evaluation of constants:@ \
       unbound identifier %s\n@]"
      (Ident.name x);
    raise Error

(* constant evaluation of size expressions *)
let size_e { values } si =
  catch (Coiteration.size (Match.liftv values) si)

(* Evaluation of an expression *)
let expression_e acc e =
  let v = Coiteration.vexp acc.gvalues (Match.liftv acc.values) e in
  catch v

(* Try to evaluate an expression; expect the result to be a boolean *)
let try_expression_bool acc e =
  let env = Match.liftv acc.values in
  let v = 
    Coiteration.try_vexp_into_bool acc.gvalues env e in
  Result.to_option v

let try_expression_e acc e =
  let env = Match.liftv acc.values in
  catch(Coiteration.try_vexp acc.gvalues env e)

(* eval a definition *)
let leq_e acc leq =
  let l_env =
    Coiteration.vleq acc.gvalues (Match.liftv acc.values) leq in
  catch l_env

(* evaluation of local definitions *)
(* [let const eq in ...] - the equations are evaluated *)
(* otherwise, they are not *)
let leq_opt_t funs acc ({ l_kind; l_eq; l_env; l_loc } as leq) =
  let ok = Typing.is_sizefun l_loc l_eq in
  match l_kind with
  | (Kstatic | Kany) when not ok -> 
     (* equations are not evaluated *)
     let l_env, acc = Mapfold.build_it funs.Mapfold.global_funs acc l_env in
     let l_eq, acc = Mapfold.equation_it funs acc l_eq in
     Some { leq with l_eq; l_env }, acc
  | _ ->
     (* evaluation of compile-time expressions *)
     let l_env = leq_e acc leq in
     (* let l = Env.to_list l_env in *)
     None, { acc with values = Env.append l_env acc.values }
  
(* Expressions *)
let expression funs acc ({ e_desc; e_loc } as e) =
  match e_desc with
  | Evar(x) ->
     (* [x] must be a compile-time constant value *)
     if Env.mem x acc.values then
       (* it is maybe already in the table of expressions *)
       if Env.mem x acc.exp then Env.find x acc.exp, acc
       else
         (* or not; then generate a declaration to compute it *)
         let v = Env.find x acc.values in
         let e, acc = exp_of e_loc funs acc v in
         e, { acc with exp = Env.add x e acc.exp }
     else
       if Env.mem x acc.renaming then
       { e with e_desc = Evar(Env.find x acc.renaming) }, acc
     else
       error { Error.kind = Eunbound_ident(x); loc = e_loc }
  | Eglobal { lname } -> 
     let l_ = Genv.show acc.gvalues in
     (* either [lname] is a constant or not *)
     let e, acc =
       try 
         let { Genv.info = v } = Genv.find_value lname acc.gvalues in
         exp_of e_loc funs acc v
       with Not_found -> e, acc in
     e, acc
  | Elet(l, e_let) ->
     let l_opt, acc = leq_opt_t funs acc l in
     let e_let, acc = Mapfold.expression_it funs acc e_let in
     { e with e_desc = Aux.opt_letdesc l_opt e_let }, acc
  | Eapp ({ is_inline; f; arg_list } as a) ->
     (* if an application need to be inlined *)
     (* it must be a compile-time constant expression *)
     let arg_list, acc = Util.mapfold (Mapfold.expression_it funs) acc arg_list in
     let f, acc = 
       if is_inline then 
         if is_immediate f then f, acc
         else
           let v = expression_e acc f in 
           exp_of f.e_loc funs acc v
       else Mapfold.expression_it funs acc f in
     { e with e_desc = Eapp { a with f; arg_list } }, acc
   | Ematch({ e; handlers } as m) ->
      (* two cases; either [e] is compile-time or not *)
      let v = try_expression_e acc e in
      let e, acc = match v with
        | None ->
           (* the evaluation fails, that is [e] is not a compile-time expression *)
           let e, acc = Mapfold.expression_it funs acc e in
           let handlers, acc =
             Util.mapfold (Mapfold.match_handler_e_it funs) acc handlers in
           { e with e_desc = Ematch { m with e; handlers } }, acc
        | Some(v) ->
           (* or it succeeds *)
           let env_pat, e = 
             catch (Match.select e_loc acc.gvalues acc.values v handlers) in
           Mapfold.expression_it funs
             { acc with values = Env.append env_pat acc.values } e in
      e, acc
  | Esizeapp { f; size_list } -> 
     (* after this step, there should be no static expressions left *)
     let v = expression_e acc f in
     let v_list = List.map (size_e acc) size_list in
     let v = Coiteration.sizeapply e_loc v v_list in
     let v = catch v in
     exp_of e_loc funs acc v
  | _ -> raise Mapfold.Fallback
  
(* Equations *)
let equation funs acc ({ eq_desc; eq_write; eq_loc } as eq) = 
  match eq_desc with
  | EQif { e; eq_true; eq_false } ->
     (* two cases; either [e] is a compile-time or not *)
     let v = try_expression_bool acc e in
     let eq, acc = match v with 
       | None ->
          (* [e] is not compile-time constant *)
          let e, acc = Mapfold.expression_it funs acc e in
          let (eq_true, eq_false), acc =
            Mapfold.if_eq_it funs acc (eq_true, eq_false) in
          { eq with eq_desc = EQif { e; eq_true; eq_false } }, acc
       | Some(b) ->
          (* [e] is *)
          if b then Mapfold.equation_it funs acc eq_true 
          else Mapfold.equation_it funs acc eq_false in
     eq, acc
  | EQmatch({ e; handlers } as m) ->
     (* two cases; either [e] is compile-time or not *)
     let v = try_expression_e acc e in
     let eq, acc = match v with
       | None ->
          (* [e] is not compile-time constant *)
          let e, acc = Mapfold.expression_it funs acc e in
          let handlers, acc =
            Util.mapfold (Mapfold.match_handler_eq_it funs) acc handlers in
          { eq with eq_desc = EQmatch { m with e; handlers } }, acc
       | Some(v) ->
          (* [e] is *)
          let env_pat, eq = 
            catch (Match.select eq_loc acc.gvalues acc.values v handlers)
          in Mapfold.equation_it funs
               { acc with values = Env.append env_pat acc.values } eq in
     eq, acc
  | EQlet(leq, eq) ->
     let leq_opt, acc = leq_opt_t funs acc leq in
     let eq, acc = Mapfold.equation_it funs acc eq in
     { eq with eq_desc = Aux.opt_eq_letdesc leq_opt eq }, acc
  | EQsizefun _ ->
     error { Error.kind = Eshould_be_static; loc = eq_loc }
  | _ -> raise Mapfold.Fallback

let letdecl_list loc acc d_leq_opt d_names =
  let add_gvalue ({ values; gvalues } as acc) (name, id) =
    try
      let v = Env.find id values in
      { acc with gvalues = Genv.add name v gvalues }
    with
    | Not_found -> assert false in
  let rename { renaming } (name, id) =
    try
      let m = Env.find id renaming in
      (name, m)
    with 
    | Not_found -> assert false in
  match d_leq_opt with
  | None ->
     (* all names define compile-time constant values *)
     (* no code is generated but the global environment is updated *)
     List.fold_left add_gvalue acc d_names
  | Some(d_leq) ->
     let d_names = List.map (rename acc) d_names in
     { acc with defs = { desc = Eletdecl { d_leq; d_names }; loc } :: acc.defs }

(* The main function. Reduce every compile-time constant definition *)
let implementation funs acc ({ desc; loc } as impl) =
  let acc =
    match desc with
    | Eopen(name) ->
       (* add [name] in the list of known modules *)
       (* load it if it exists *)
       (* This is a temporary solution: it uses two distinct tables *)
       (* one for storing type informations; one for storing values. I *)
       (* should take the solution used version 2, with a unique table *)
       { acc with gvalues = Genv.try_to_open_module acc.gvalues name;
                  defs = impl :: acc.defs }
    | Eletdecl { d_names; d_leq } ->
       (* [d_leq] must be either constant or static *)
       let d_leq_opt, acc = leq_opt_t funs acc d_leq in
       letdecl_list loc acc d_leq_opt d_names
    | Etypedecl _ -> { acc with defs = impl :: acc.defs } in
  impl, acc

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let program otc gvalues { p_impl_list; p_index } =
  let global_funs = 
    { Mapfold.default_global_funs with build; var_ident } in
  let funs =
    { Mapfold.defaults with expression; equation; implementation; global_funs }
  in
  let acc = { empty with gvalues } in

  let l_ = Genv.show gvalues in

  let n, acc = Mapfold.set_index_it funs acc p_index in
  let _, { gvalues; defs } = 
    Util.mapfold (Mapfold.implementation_it funs) acc p_impl_list in
  let p_index, acc = Mapfold.get_index_it funs acc n in
  
  let l_ = Genv.show gvalues in

  (* store the value into the table of values *)
  apply_with_close_out (Genv.write gvalues) otc;
  (* definitions in [defs] are in reverse order *)
  let p_impl_list = List.rev defs in
  { p_impl_list; p_index }
