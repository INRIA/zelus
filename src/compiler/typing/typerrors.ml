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

(* Printing of error messages during typing *)
(* messages are displayed on the standard error output *)

open Misc
open Ident
open Location
open Modules
open Deftypes
open Ptypes
open Format

type kind_of_global_ident = Value | Type | Constr | Label

type kind_of_ident = | Current | Initial | Derivative

type error =
  | Evar_undefined of Ident.t
  | Emissing of Ident.t
  | Eglobal_undefined of kind_of_global_ident * Lident.t
  | Eglobal_already of kind_of_global_ident * string
  | Ealready of kind_of_ident * Ident.t
  | Ealready_with_different_kinds of kind_of_ident * kind_of_ident * Ident.t
  | Eis_a_value of Ident.t
  | Einit_undefined of Ident.t
  | Elast_forbidden of Ident.t
  | Eshould_be_a_signal of Ident.t * typ
  | Ecannot_be_set of bool * Ident.t
  | Etype_clash of typ * typ
  | Etype_vkind_clash of vkind * typ
  | Earity_clash of int * int
  | Estate_arity_clash of Ident.t * int * int
  | Estate_unbound of Ident.t
  | Estate_initial
  | Ekind_should_not_be_combinatorial
  | Ekind_clash of kind * kind
  | Esome_labels_are_missing
  | Eequation_is_missing of Ident.t
  | Eglobal_is_a_function of Lident.t
  | Eapplication_of_non_function
  | Epattern_not_total
  | Enot_a_size_expression
  | Esize_is_undetermined 
  | Esize_of_vec_is_undetermined
  | Esize_clash of Defsizes.rel * Defsizes.exp * Defsizes.exp
  | Esize_constraints_not_true of 
      (* [top_sc[... nested_sc ...] *)
      { f_loc_list: Location.ft list;
        (* list of file/location to the error *)
        top_sc: Defsizes.exp Defsizes.constraints;
        (* unsatisfied constraint *)
        nested_env: int Env.t; (* the local environment *)
        nested_sc: Defsizes.exp Defsizes.constraints;
        (* the nested unsatisfied constraint *)
      }
  | Esize_parameter_cannot_be_generalized of Ident.t * typ
  | Esize_parameter_mutually_recursive_definitions of int * int
  | Econstr_arity of Lident.t * int * int
  | Esizefun_and_equations_are_mixed

exception Error of Location.t * error
				
let error loc kind = raise (Error(loc, kind))
                       
type 'info warning =
  | Wpartial_matching of  'info Zelus.pattern
  | Wunreachable_state of Ident.t
  | Wmatch_unused of 'info Zelus.pattern
  | Wequation_does_not_define_a_name
  | Wreset_target_state of bool * bool
    		       
let kind_of_global_ident k = match k with
    | Value -> "value" | Type -> "type" 
    | Constr -> "constructor" | Label -> "label"

let kind_of_ident k =
  match k with
  | Current -> "value"
  | Derivative -> "derivative"
  | Initial -> "initial value"
                        
let vkind_message = function
    | Tconst -> "compile time constant"
    | Tstatic -> "static" | Tany -> "combinational"

let kind_message = function
  | Tfun(k) -> vkind_message k
  | Tnode(k) -> (match k with | Tdiscrete -> "node" | Tcont -> "hybrid node")
  		
let message loc kind =
  begin match kind with
  | Evar_undefined(name) ->
     eprintf "@[%aType error: The value identifier %s is unbound.@.@]"
             output_location loc (Ident.source name)
  | Emissing(s) ->
     eprintf "@[%aType error: no equation is given for name %s.@.@]"
        output_location loc
        (Ident.source s);
  | Eglobal_undefined(k, lname) ->
     eprintf
       "@[%aType error: the global value identifier %s %s is unbound.@.@]"
            output_location loc (kind_of_global_ident k)
            (Lident.modname lname)
  | Eglobal_already(k, s) ->
      eprintf "@[%aType error: the %s name %s is already defined.@.@]"
        output_location loc (kind_of_global_ident k) s 
  | Ealready(k, s) ->
     let k = kind_of_ident k in
     eprintf
       "@[%aType error: the identifier %s, with kind %s, is defined twice.@.@]"
        output_location loc (Ident.source s) k
  | Ealready_with_different_kinds(k1, k2, s) ->
     let k1 = kind_of_ident k1 in
     let k2 = kind_of_ident k2 in
     eprintf
       "@[%aType error: %s is defined twice in a parallel branch,@,\
                once as a %s, once as a %s.@.@]"
        output_location loc (Ident.source s) k1 k2
  | Einit_undefined(s) ->
      eprintf "@[%aType error: %s must be initialized in every branch.@.@]"
        output_location loc
        (Ident.source s)
  | Eis_a_value(s) ->
      eprintf "@[%aType error: last %s is forbidden as %s is a value.@.@]"
        output_location loc
        (Ident.source s) (Ident.source s)
  | Elast_forbidden(s) ->
     eprintf
       "@[%aType error: last %s is forbidden. This is either @,\
        because %s is not a state variable or next %s is defined.@.@]"
       output_location loc
       (Ident.source s) (Ident.source s) (Ident.source s)
  | Eshould_be_a_signal(s, expected_ty) ->
      eprintf "@[%aType error: the variable %s of type %a is defined by case \
                   but one case is missing. \n\
                   Either define the variable as a signal or \
                   give a initial or default value.@.@]"
        output_location loc
        (Ident.source s)
	Ptypes.output_type expected_ty
  | Ecannot_be_set(is_next, s) ->
      eprintf "@[%aType error: the %s value of %s cannot be set. @,\
                 This is either because the %s value is set or @,\
                 the last value is used.@.@]"
        output_location loc
        (if is_next then "next" else "current")
	(Ident.source s)
	(if is_next then "current" else "next")
  | Etype_clash(actual_ty, expected_ty) ->
      eprintf "@[%aType error: this expression has type@ %a,@ \
               but is expected to have type@ %a.@.@]"
        output_location loc
        Ptypes.output_type  actual_ty
        Ptypes.output_type  expected_ty
  | Etype_vkind_clash(vkind, actual_ty) ->
      eprintf "@[%aType error: this expression has type@ %a,@ \
               which does not belong to the %s kind.@.@]"
        output_location loc
        Ptypes.output_type  actual_ty
        (vkind_message vkind)
  | Earity_clash(actual_arit, expected_arit) ->
      eprintf "@[%aType error: this expression expects %d arguments,@ \
               but is given %d arguments.@.@]"
        output_location loc
        expected_arit actual_arit
  | Estate_arity_clash(name, actual_arit, expected_arit) ->
      eprintf "@[%aType error: the state %s expects %d arguments,@ \
               but is given %d arguments.@.@]"
        output_location loc
        (Ident.source name)
        expected_arit actual_arit
  | Estate_unbound(name) ->
      eprintf
        "@[%aType error: the state %s is unbound in the current automaton.@.@]"
        output_location loc
        (Ident.source name)
  | Estate_initial ->
      eprintf
        "@[%aType error: the initial state cannot be parameterized.@.@]"
        output_location loc
  | Ekind_should_not_be_combinatorial ->
      eprintf
        "@[%aType error: this expression should not be combinatorial.@.@]"
        output_location loc
 | Ekind_clash(actual_kind, expected_kind) ->
       eprintf
        "@[%aType error: this is a %s expression@ but is expected to be %s.@.@]"
        output_location loc
        (kind_message actual_kind) (kind_message expected_kind)
 | Esome_labels_are_missing ->
      eprintf
        "@[%aType error: some fields are missing.@.@]"
        output_location loc
 | Eequation_is_missing(name) ->
     eprintf
       "@[%aType error: the variable %s must be defined in an equation.@.@]"
       output_location loc
       (Ident.source name)
 | Eglobal_is_a_function(lname) ->
     eprintf "@[%aType error: the global name %s must not be a function.@.@]"
        output_location loc
        (Lident.modname lname)
 | Eapplication_of_non_function ->
     eprintf "@[%aType error: this is not a function.@.@]"
        output_location loc
 | Epattern_not_total ->
     eprintf
       "@[%aType error: this pattern must be total.@.@]"
       output_location loc
 | Esize_is_undetermined ->
    eprintf
      "@[<hov 0>%aType error: the size cannot be determined at that point.@.@]"
      output_location loc
 | Esize_of_vec_is_undetermined ->
    eprintf
      "@[<hov 0>%aType error: this expression is either not a vector@ or its \
       size cannot be determined at that point.@.@]"
      output_location loc
 | Enot_a_size_expression ->
    eprintf
      "@[%aType error: this is not a size.@.@]"
      output_location loc
 | Esize_clash(cmp, actual_size, expected_size) ->
    let s = match cmp with
      | Defsizes.Eq -> "equal to" | Defsizes.Lt -> "strictly less than"
      | Defsizes.Lte -> "less of equal to" in
    eprintf "@[%aType error: this expression is equal to@ %a,@ \
               but is expected to be %s@ %a.@.@]"
        output_location loc
        Ptypes.output_size actual_size
        s
        Ptypes.output_size expected_size
 | Esize_parameter_cannot_be_generalized(n, ty) ->
     eprintf
       "@[%aType error: this pattern has type@ %a,@ \
        which contains the variable %s that is unbounded.@.@]"
	output_location loc
        Ptypes.output_type ty
	(Ident.name n)
 | Esize_parameter_mutually_recursive_definitions
    (expected_number, actual_number) ->
    eprintf
      "@[%aType error: the number of size parameters must be the same\n\
       in mutually recursive definitions of size functions.\n\
       (this function has %d parameters while one has %d parameters).@.@]"
      output_location loc
      actual_number expected_number
 | Esize_constraints_not_true { f_loc_list; top_sc; nested_env; nested_sc } ->
    let output_location_list ff f_loc_list =
      match f_loc_list with
      | [] -> ()
      | _ -> Format.fprintf ff
               "@[This constraint is generated during the typing of \
                the following expressions:@ @[%a@]@,@]"
               Location.output_location_list f_loc_list in
    eprintf
      "@[<hov0>%aType error: at this point, the following \
       size constraint is false:@[%a@]@,\
       This is because the following size constraint is false:\n@[%a@]@,\
       where the value for the free size and index variables in@ %a@ \
       is:\n@[%a@]@,\
       %a@\n\
       Overall, a size constraint is false because:@ \
       - an array element is accessed out of the bounds, or@,\
       - the actual size of an array does not match an expected size, or@,\
       - the size argument of a recursive function does not \
       decrease strictly @ for the lexicographic order.@.@]"
       output_location loc
       Ptypes.constraints_t top_sc
       Ptypes.constraints_t nested_sc
       Ident.S.fprint_t
         (Sizes.fv_constraints Ident.S.empty Ident.S.empty nested_sc)
       (Ident.Env.fprint_t (fun ff -> Format.fprintf ff "%d")) nested_env
       output_location_list f_loc_list
 | Econstr_arity(ln, expected_arity, actual_arity) ->
     let module Printer = Printer.Make(Typinfo) in
     eprintf
       "@[%aType error: the type constructor %a expects %d argument(s),@ \
        but is here given %d arguments(s).@.@]"
       output_location loc
       Printer.longname ln
       expected_arity
       actual_arity
 | Esizefun_and_equations_are_mixed ->
    eprintf
      "@[%aType error: definitions of (stream) equations and size functions \
       are mixed.@.@]"
       output_location loc
  end;
  raise Misc.Error

    
let warning loc w =
  let module Printer = Printer.Make(Typinfo) in
  if not !Misc.no_warning then
  match w with
  | Wpartial_matching(p) ->
      Format.eprintf
        "@[%aType warning: this pattern-matching is not exhaustive.@.@]"
	output_location loc;
      Format.eprintf
        "@[Here is an example of a value that is not matched:@.%a@.@]"
	Printer.pattern p
  | Wunreachable_state(s) ->
     eprintf
       "@[%aType warning: the state %s in this automaton is unreachable.@.@]"
       output_location loc
       (Ident.source s)
  | Wmatch_unused(p) ->
      Format.eprintf
        "@[Type warning: match case \"%a\" is unused.@.@]" Printer.pattern p
  | Wequation_does_not_define_a_name ->
     eprintf
       "@[%aType warning: this equation does not define a name. \
          This looks like deadcode.@.@]"
       output_location loc
  | Wreset_target_state(actual_reset, expected_reset) ->
      eprintf
        "@[%aType warning: the target state is expected to be %s,@,\
             but is entered by %s.@.@]"
       output_location loc
       (if expected_reset then "reset" else "on history")
       (if actual_reset then "reset" else "history")
 
