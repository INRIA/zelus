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
(* causality type system and use causality tags to decide whether *)
(* a function needs to be inlined or not *)

(* Example: *)
(* First-order:
 *- [val euler_forward : 'a * 'b -> 'a]
 *- [val euler_backward : 'a * 'a -> 'a]
 *- fixpoint: [rec sin = euler_forward(0.0, cos)
 *-            and cos = euler_backward(1.0, -. sin)]
 *- The call to [euler_backward(1.0, -. sin)] must be inlined.
 *- the equation is rewritten
 *- [rec sin = euler_forward(0.0, cos)
 *-  and cos = inline euler_backward(1.0, -. sin)] *)
(* Higher-order:
 *- [fun f x -> rec y = f x y]
 *- the call [f x y] must be inlined. the expression is rewritten into:
 *- [fun f x -> rec y = inline f x y] *)

(* Given a expression [fun arg1 ... argn -> e]
 *- with type [t = t1 -> ... tn -> te]
 *- compute its input and outputs tags, that is, I(t) and O(t)
 *- let [f e1...ek] a function call that appear in the body [e]
 *- with [f: t0], [ei: ti] and [f e1...ek : tres]
 *- computes O(ti)_{i in [0..k] and O(tres)
 *- [f e1 ... ek] is inlined if the following holds: 
 *- not [forall{i in out_of_inputs}
             forall{j in out_of_result}
               { (IO(i) subset IO(j)) && not (strict_path o i) }]
 *- otherwise, it is rewritten [inline f e1 ... ek] *)
 
(* Algorithm:
 *- for every function [fun arg1 ... argn -> e], compute
 *- the I and O sets. Recursively traverse the body [e] and collect the
 *- causality tags
 *)
open Zelus

type table =
  { inputs: Tcausal.S.t; (* the causality tags of inputs of the function *)
    outputs: Tcausal.S.t; (* the causality tags of outputs *)
    o_table: Tcausal.S.t Tcausal.M.t; (* outputs of a causality tag *)
    io_table: Tcausal.S.t Tcausal.M.t; (* the IO relation for all *)
                                     (* accessible causality tags in the body *)
   }
  
(* [to_inline] The function which decides that a function call *)
(* [f arg1 ... argn] must be inlined or not *)
let to_inline ({ inputs; outputs; io_table; o_table } as table) (tc_arg_list, tc_res) =
  let _, out_of_inputs =
    List.fold_left
      (Tcausal.ins_and_outs_of_a_type true) (Tcausal.S.empty, Tcausal.S.empty)
      tc_arg_list in
  let _, out_of_result =
    Tcausal.ins_and_outs_of_a_type true (Tcausal.S.empty, Tcausal.S.empty)
      tc_res in
  (* computes the [io] *)
  let io_table =
    Tcausal.S.fold (Tcausal.update_io_table inputs o_table) out_of_inputs io_table in
  let io_table =
    Tcausal.S.fold (Tcausal.update_io_table inputs o_table) out_of_result io_table in

  (* [f arg1 ... argn] is inlined if:
   *- not [forall{i in out_of_inputs}
             forall{j in out_of_result}
               { (IO(i) subset IO(j)) && not (strict_path o i) }] *)
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
         out_of_inputs),
  { table with io_table }

(* Given a function definition [fun f_args -> body] *)
(* compute the set of causality tags that appear as input/outputs *)
let funexp_build_table { f_args; f_body = { r_info } } =
  let tc = Typinfo.get_caus r_info in
  
  (* mark inputs/outputs *)
  Tcausal.mark_and_polarity true tc;
  let c_set = Tcausal.vars Tcausal.S.empty tc in
  let inputs, outputs = Tcausal.ins_and_outs c_set in
  
  (* compute the table of outputs for all the variables *)
  let o_table = Tcausal.build_o_table c_set Tcausal.M.empty in

  (* then the table of io for every causality tag *)
  { inputs = inputs;
    outputs = outputs;
    io_table = Tcausal.M.empty;
    o_table = o_table }
  
(* Mark function calls in the body of [fun f_args -> body] to be inlined *)
let funexp_apply_table table ({ f_body } as f) =
  (* traverse expressions *)
  let expression funs table ({ e_desc; e_info } as e) =
    match e_desc with
    | Eapp { is_inline = false; f; arg_list } ->
       let tc_res = Typinfo.get_caus e_info in
       let tc_arg_list =
         List.map
           (fun { e_info } -> Typinfo.get_caus e_info) (f :: arg_list) in
       let is_inline, table = to_inline table (tc_arg_list, tc_res) in
       { e with e_desc = Eapp({ is_inline; f; arg_list }) }, table
    | _ -> raise Mapfold.Fallback in
  let global_funs = Mapfold.default_global_funs in
  let funs = { Mapfold.defaults with expression; global_funs } in
  let f_body, table = Mapfold.result_it funs table f_body in
  { f with f_body }, table

let funexp funs _ f =
  let table = funexp_build_table f in
  let f, _ = funexp_apply_table table f in
  f, ()

let program p =
  let global_funs = Mapfold.default_global_funs in
  let funs =
    { Mapfold.defaults with funexp; global_funs } in
  let { p_impl_list } as p, _ =
    Mapfold.program_it funs () p in
  { p with p_impl_list = p_impl_list }


    
