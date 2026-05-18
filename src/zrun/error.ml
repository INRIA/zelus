(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2026 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Location
open Format

type kind =
  | Etype : typ_error option -> kind (* type error for values *)
  | Estate : kind (* type error for states *)
  | Eunbound_ident : Ident.t -> kind (* unbound variable *)
  | Eunbound_last_ident : Ident.t -> kind (* unbound last variable *)
  | Eunbound_lident : Lident.t -> kind (* unbound global variable *)
  | Eundefined_ident : Ident.t -> kind (* no definition is given *)
  | Eshould_be_a_node : kind (* the expression should return a node *)
  | Eshould_be_static : kind
  | Eshould_be_combinatorial : kind
  (* the maximum number of fix-point iteration has been reached *)
  | Efixpoint_limit : kind
  (* the expression should be combinatorial *)
  | Eand_non_linear : Ident.t  -> kind (* [x] appears twice *)
  | Eno_default : Ident.t -> kind (* no default value is given to [x] *)
  | Einitial_state_with_parameter : Ident.t  -> kind
  (* the initial state has a parameter which is undefined *)
  | Epattern_matching_failure : kind
  | Enil : kind (* value is nil *)
  | Ebot : kind (* value is bottom *)
  | Eequal : kind (* values that are expected to be equal are not *)
  | Eassert_failure : kind (* assertion is not true *)
  | Emerge_env : { init: bool; id: Ident.t } -> kind
  (* two equations define a common name *)
  | Erecursive_value : kind (* recursive value definition *)
  | Enot_causal : Ident.S.t -> kind (* a set of variables whose value is bot *)
  | Earray_index : { size : int; index : int } -> kind
  | Earray_slice : { size : int; i1 : int; i2 : int } -> kind
  (* the array is of size [size] but accessed out-of-bound, at index > size *)
  | Eloop_index : { size : int; index : int } -> kind
  (* the loop has [size] iterations but the index is of a different size *)
  | Eloop_no_iteration : kind
  (* the size must decrease at every recursive call *)
  | Esize_in_a_recursive_call : { actual: int list; expected: int list } -> kind
  (* recursive definitions must be either sets of functions parameterized *)
  (* by a size or do not contain such functions *)
  | Esizefun_def_recursive : kind
  (* the loop should iterate at least once; or give a default value *)
  | Eloop_cannot_determine_size : kind
  (* the size is not given and there is no input *)
  | Earray_cannot_be_filled : { name: Ident.t;
                                size : int;
                                nb_of_missing_iterations : int } -> kind
  (* the returned value for [id] should be an array of size [size]; *)
  (* [missing] elements are missing *)
  | Earray_dimension_in_iteration : { expected_dimension: int;
                                      actual_dimension: int } -> kind
  (* the loop iterates on [expected_dimensions] but the input or output array *)
  (* has dimention [actual_dimension] *)
  | Eunexpected_failure : { print : formatter -> 'a -> unit; arg : 'a } -> kind
  (* an error that should not arrive *)
  | Enot_implemented : kind (* not implemented *)

(* the possible type errors *)
and typ_error =
  | Etyp_bool | Etyp_int | Etyp_float (* a boolean, int, float is expected *)
  | Etyp_array (* an array is expected *)
  | Etyp_fun (* a function is expected *)
  | Etyp_signal (* a signal is expected *)
  | Etyp_record of typ_record_error
  | Etyp_state_in_automaton (* it should be a state of the automaton *)
  | Etyp_pvalue (* it should be a value (that is, neither bot nor nil *)
                   
and typ_record_error =
  | Etyp_record_access of Lident.t (* a record is expected with label [l] *)
  | Etyp_record_build
  | Etyp_record_with

type error = { kind : kind; loc : Location.t }

let unexpected_failure =
  Eunexpected_failure { arg = (); print = fun ff () -> () }

let message loc kind =
  match kind with
  | Eunbound_ident(name) ->
     eprintf "@[%aZrun: the value identifier %s is unbound.@.@]"
       output_location loc (Ident.source name)
  | Eunbound_last_ident(name) ->
     eprintf "@[%aZrun: The last value identifier %s is unbound.@.@]"
       output_location loc (Ident.source name)
  | Eunbound_lident(lname) ->
     eprintf "@[%aZrun: the global value identifier %s is unbound.@.@]"
       output_location loc (Lident.modname lname)
  | Eundefined_ident(name) ->
     eprintf
       "@[%aZrun: the identifier %s is declared but it has no definition.@.@]"
       output_location loc (Ident.source name)
  | Etype(ty_opt) ->
     let typ_error ff ty =
       match ty with
       | Etyp_bool -> fprintf ff "bool"
       | Etyp_int -> fprintf ff "int"
       | Etyp_float -> fprintf ff "float"
       | Etyp_array -> fprintf ff "array"
       | Etyp_fun -> fprintf ff "function"
       | Etyp_signal -> fprintf ff "signal"
       | Etyp_state_in_automaton -> fprintf ff "state in an automaton"
       | Etyp_pvalue -> fprintf ff "value must be neither nil nor bot"
       | Etyp_record(error) ->
          match error with
          | Etyp_record_access(lname) ->
             fprintf ff "label %s in record is missing" (Lident.modname lname)
          | Etyp_record_build 
            | Etyp_record_with -> fprintf ff "record" in
     let typ_error_opt ff ty_opt =
       match ty_opt with
       | None -> () | Some(ty) -> fprintf ff " (%a)" typ_error ty in
     eprintf "@[%aZrun: the actual and the expected type%a do not match.@.@]"
       output_location loc typ_error_opt ty_opt
  | Estate ->
     eprintf "@[%aZrun: actual and expected state do not match.@.@]"
       output_location loc 
  | Eshould_be_a_node ->
     eprintf "@[%aZrun: this expression should return a node.@.@]"
       output_location loc 
  | Eshould_be_static ->
     eprintf "@[%aZrun: this expression should be static.@.@]"
       output_location loc 
  | Eshould_be_combinatorial ->
     eprintf "@[%aZrun: this expression should be combinatorial.@.@]"
       output_location loc 
  | Efixpoint_limit ->
     eprintf "@[%aZrun: the maximum number of iteration for computing the\
              fixpoint has been reached.@.@]"
       output_location loc 
 | Eand_non_linear(name) ->
     eprintf
       "@[%aZrun: the identifier %s is defined twice in a \
        two parallel branches.@.@]"
       output_location loc (Ident.source name)
  | Eno_default(name) ->
     eprintf
       "@[%aZrun: no default value is given to %s.@.@]"
       output_location loc (Ident.source name)
  | Einitial_state_with_parameter(name) ->
     eprintf "@[%aZrun: the initial state %s has a parameter which is \
              undefined.@.@]"
       output_location loc (Ident.source name)
  | Epattern_matching_failure ->
     eprintf "@[%aZrun: pattern matching failure.@.@]" output_location loc
  | Enot_implemented ->
     eprintf "@[%aZrun: not implemented.@.@]" output_location loc
  | Enil ->
     eprintf "@[%aZrun: value is nil.@.@]" output_location loc
  | Ebot ->
     eprintf "@[%aZrun: value is bottom.@.@]" output_location loc
  | Eequal ->
     eprintf "@[%aZrun: equality is not defined for these inputs.@.@]"
       output_location loc
  | Eassert_failure ->
     eprintf "@[%aZrun: assertion is not true.@.@]" output_location loc
  | Emerge_env { init; id } ->
     eprintf "@[%aZrun: two parallel equations are given for %s%s.@.@]"
       output_location loc (if init then "the initial value of " else "")
       (Ident.source id)
  | Erecursive_value ->
     eprintf
       "@[%aZrun: the recursive definition of a value is not allowed.@.@]"
       output_location loc
  | Enot_causal(bot_names) ->
     let pnames ff names =
       let l = Ident.S.to_list names in
       Pp_tools.print_list_r Ident.fprint_t "{" "," "}" ff l in
     eprintf "@[%aZrun: the following variables are not causal:\n\
              %a@.@]"
       output_location loc
       pnames bot_names
  | Earray_index { size; index } ->
     eprintf "@[%aZrun: the array is of length %d but accessed at index %d.@.@]"
       output_location loc size index
  | Earray_slice { size; i1; i2 } ->
     eprintf "@[%aZrun: the array is of length %d but sliced from %d to %d.@.@]"
       output_location loc size i1 i2
  | Eloop_index { size; index } ->
     eprintf
       "@[%aZrun: the loop has %d iterations but the index is of lenfth %d.@.@]"
       output_location loc size index
  | Eloop_no_iteration ->
     eprintf
       "@[%aZrun: the loop has no iteration. Either give a default value\
        or ensure there is at least one iteration.@.@]"
       output_location loc
  | Esize_in_a_recursive_call { actual; expected } ->
     let print_v_list ff v_list =
       Pp_tools.print_list_l
         (fun ff i -> Format.fprintf ff "%d" i) "(" "," ")" ff v_list in
     eprintf
       "@[%aZrun: the actual value of the size parameter is %a \n\
        whereas it should be strictly less than %a and non negative.@.@]"
       output_location loc print_v_list actual print_v_list expected
  | Esizefun_def_recursive ->
     eprintf
       "@[%aZrun: values defined recursively can only be\n\
        functions parameterized by a size or streams.@.@]"
       output_location loc
  (* the loop should iterate at least once; or give a default value *)
  | Eloop_cannot_determine_size ->
    eprintf
       "@[%aZrun: the number of iterations of the loop cannot be determined.@.@]"
       output_location loc
  | Earray_cannot_be_filled { name; size; nb_of_missing_iterations } ->
     eprintf
     "@[%aZrun: the result should be an array of size %d but %d elements are\
        missing. Either declare %s with an init or a default value.@.@]"
      output_location loc size nb_of_missing_iterations (Ident.source name)
  | Earray_dimension_in_iteration { expected_dimension; actual_dimension } ->
    eprintf
      "@[%aZrun: the number of dimensions for the result is %d\n
       while the loop iterates on %d dimensions.@.@]"
      output_location loc actual_dimension expected_dimension
  (* the loop iterates on [expected_dimensions] but the input or output array *)
  (* has dimention [actual_dimension] *)
  | Eunexpected_failure { print; arg } ->
     eprintf "@[%aZrun: unexpected error.@.%a@.@]" output_location loc print arg
