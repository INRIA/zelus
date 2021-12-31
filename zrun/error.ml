(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
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
  | Etype : kind (* type error for values *)
  | Estate : kind (* type error for states *)
  | Eunbound_ident : Ident.t -> kind (* unbound variable *)
  | Eunbound_last_ident : Ident.t -> kind (* unbound last variable *)
  | Eunbound_lident : Lident.t -> kind (* unbound global variable *)
  | Eundefined_ident : Ident.t -> kind (* no definition is given *)
  | Eshould_be_a_node : kind (* [x] should be a node *)
  | Eshould_be_a_function : kind (* [x] should be a value *)
  | Eand_non_linear : Ident.t  -> kind (* [x] appears twice *)
  | Eno_default : Ident.t -> kind (* no default value is given to [x] *)
  | Einitial_state_with_parameter : Ident.t  -> kind
  (* the initial state has a parameter which is undefined *)
  | Epattern_matching_failure : kind
  | Enot_implemented : kind (* not implemented *)
  | Enil : kind (* value is nil *)
  | Ebot : kind (* value is bottom *)
  | Eassert_failure : kind (* assertion is not true *)
  | Emerge_env : kind (* two equations have names in common *)
  | Erecursive_value : kind (* recursive value definition *)
  | Enot_causal : Ident.S.t -> kind (* a set of variables whose value is bot *)
  | Eunexpected_failure : kind (* an error that should not arrive *)
                      
type error = { kind : kind; loc : Location.t }
           
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
  | Etype ->
     eprintf "@[%aZrun: actual and expected types do not match.@.@]"
       output_location loc 
  | Estate ->
     eprintf "@[%aZrun: actual and expected state do not match.@.@]"
       output_location loc 
  | Eshould_be_a_node ->
     eprintf "@[%aZrun: this expression should return a node.@.@]"
       output_location loc 
  | Eshould_be_a_function ->
     eprintf "@[%aZrun: this expression should return a function.@.@]"
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
  | Eassert_failure ->
     eprintf "@[%aZrun: assertion is not true.@.@]" output_location loc
  | Emerge_env ->
     eprintf "@[%aZrun: the two equations have defined names in common.@.@]"
       output_location loc
  | Erecursive_value ->
     eprintf
       "@[%aZrun: the recursive definition of a value is not allowed.@.@]"
       output_location loc
  | Enot_causal(bot_names) ->
     let pnames ff names = Ident.S.iter (Ident.fprint_t ff) names in
     eprintf "The following variables are not causal:\n\
              %a@." pnames bot_names
  | Eunexpected_failure ->
     eprintf "@[%aZrun: unexpected error.@.@]" output_location loc

