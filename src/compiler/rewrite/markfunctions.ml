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

(* Mark functions to be inlined. The analysis is based on the *)
(* causality type system and use the causality tags to decide whether *)
(* a function must be inlined or not *)

open Zelus

type io_table =
  { inputs: Tcausal.S.t; (* the causality tags of inputs of the function *)
    outputs: Tcausal.S.t; (* the causality tags of outputs *)
    o_table: Tcausal.S.t Tcausal.M.t; (* outputs of a causality tag *)
    io_table: Tcausal.S.t Tcausal.M.t; (* the IO relation for all *)
                                     (* accessible causality tags in the body *)
   }
  
(* For that purpose:
 *- 1/ a first pass computes the set of causality tags
 *- that appear in the body of a function; 
 *- 2/ then the IO for all of them;
 *- 3/ if a function call [f arg1...argn] has to be inlined because, otherwise
 *- it would prevent a correct feed-back loop, it 
 *- is rewritten into [inline f arg1...argn].
 *- the decision is made according to the causality type.
 *- (see the [to_inline] function)
 *- Intuition:
 *- let [f: tc0; arg1: tc1;...; argn: tcn] and [f arg1...argn : tc_res]
 *- The function call is not inlined 
 *- if forall ai, bj st ai in Out tcj, bj in tc_res.
 *-      (io(bj) subseteq io(ai) or io(ai) subseteq io(bj)) and not bj <* ai 
 *- <* is the reflexive/transitive closure of <;
 *- io(a) is the input/dependences of a, with i(a) a subset of names 
 *- from vars tc_in_list and o(a) a subset of names from vars tc_out 
 *- otherwise, the function is inlined 
 *- In such a case, the function call is strict, that is, 
 *- all outputs of the function call already depend 
 *- on all of its inputs *)

(* Given a function definition [fun f_args -> body] *)
(* compute the set of causality tags that appear as input/outputs *)
(* of function applications inside the body *)
let funexp_build_io_table { f_args; f_body = ({ r_info } as r) } =
  (* traverses the body *)
  let result c_set r =
    let expression funs c_set ({ e_desc; e_info } as e) =
      match e_desc with
      | Eapp { f; arg_list } ->
         let _, c_set =
           Util.mapfold (Mapfold.expression_it funs) c_set arg_list in
         (* compute the set of causality tags *)
         let tc_list =
           List.map (fun { e_info } -> Typinfo.get_caus e_info) (arg_list) in
         let tc = Typinfo.get_caus f.e_info in
         let c_set =
           List.fold_left Tcausal.vars (Tcausal.vars c_set tc) tc_list in
         e, c_set
      | _ -> Mapfold.expression funs c_set e in
    let global_funs = Mapfold.default_global_funs in
    let funs =  { Mapfold.defaults with expression; global_funs } in
    let _, c_set = Mapfold.result_it funs c_set r in
    c_set in

  (* Compute the inputs/outputs causality types of the function *)
  let tc_list =
    let arg acc a =
      List.fold_left
        (fun acc { var_info } -> Typinfo.get_caus var_info :: acc) acc a in
    List.fold_left arg [] f_args in
  
  let tc = Typinfo.get_caus r_info in
  
  (* mark inputs/outputs *)
  List.iter (Tcausal.mark_and_polarity false) tc_list;
  Tcausal.mark_and_polarity true tc;
  let c_set =
    Tcausal.vars (List.fold_left Tcausal.vars Tcausal.S.empty tc_list) tc in
  let inputs, outputs = Tcausal.ins_and_outs c_set in
  (* computes the set of causality tags that appear in [f_body] *)
  let c_set = result c_set r in

  (* compute the table of outputs for all the variables *)
  let o_table = Tcausal.build_o_table c_set Tcausal.M.empty in

  (* then the table of io for every causality tag *)
  let io_table = Tcausal.build_io_table inputs o_table c_set Tcausal.M.empty in
  { inputs = inputs;
    outputs = outputs;
    io_table = io_table;
    o_table = o_table }
  
(* [to_inline] The function which decides whether or not a function call *)
(* [f(arg1,...,argn) must be inlined *)
let to_inline { io_table; o_table } tc_arg_list tc_res =
  let _, out_of_inputs =
    List.fold_left
      (Tcausal.ins_and_outs_of_a_type true) (Tcausal.S.empty, Tcausal.S.empty)
      tc_arg_list in
  let _, out_of_result =
    Tcausal.ins_and_outs_of_a_type true (Tcausal.S.empty, Tcausal.S.empty)
      tc_res in
  (* inline if not [\/_{i in out_of_inputs} IO(i) 
                    subset /\_{j in out_of_result} IO(j)] *)
  (*                or exists o in out_of_result, i in out_of_inputs. path o i *)
  (* if [inline = false], add extra dependences so that all output of the *)
  (* result depends on all inputs. *)
  let inline =
    not (Tcausal.S.for_all
           (fun i ->
             let io_of_i =
	       try Tcausal.M.find i io_table with Not_found -> Tcausal.S.empty in
             Tcausal.S.for_all
               (fun o ->
                 try
		   let io_of_o = Tcausal.M.find o io_table in
                   not (Tcausal.strict_path o i) &&
                     (Tcausal.S.subset io_of_i io_of_o)
	         with Not_found -> true)
               out_of_result)
           out_of_inputs) in
  try
    if not inline then
      Tcausal.S.iter
        (fun i ->
          Tcausal.S.iter
            (fun o -> if not (Tcausal.equal i o) then Tcausal.less_c i o)
            out_of_result)
        out_of_inputs;
    inline
  with
  | Tcausal.Clash _ -> assert false

(* Mark function calls to be inlined *)
let funexp_apply_io_table io_table ({ f_body } as f) =
  (* expressions *)
  let expression funs acc ({ e_desc; e_info } as e) =
    match e_desc with
    | Eapp { is_inline; f; arg_list } ->
       (* only fully applied functions can be inlined *)
       let op, _ = Mapfold.expression_it funs acc f in
       let arg_list, _ =
         Util.mapfold (Mapfold.expression_it funs) acc arg_list in
       let is_inline =
         if is_inline then true
         else
           let tc_res = Typinfo.get_caus e_info in
           let tc_arg_list =
             List.map
               (fun { e_info } -> Typinfo.get_caus e_info) (op :: arg_list) in
           to_inline io_table tc_arg_list tc_res in
       { e with e_desc = Eapp({ is_inline; f; arg_list }) }, acc
    | _ -> Mapfold.expression funs acc e in
  let global_funs = Mapfold.default_global_funs in
  let funs =  { Mapfold.defaults with expression; global_funs } in
  let f_body, _= Mapfold.result_it funs () f_body in
  { f with f_body }, io_table

let funexp funs _ f =
  let io_table = funexp_build_io_table f in
  let f, _ = funexp_apply_io_table io_table f in
  f, ()

let program p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with funexp; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs () p in
  { p with p_impl_list = p_impl_list }


    
