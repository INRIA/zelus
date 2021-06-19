(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2021 Inria Paris (see the AUTHORS file)                        *)
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
  | Eis_a_value of Ident.t
  | Einit_undefined of Ident.t
  | Elast_forbidden of Ident.t
  | Eshould_be_a_signal of Ident.t * typ
  | Ecannot_be_set of bool * Ident.t
  | Etype_clash of typ * typ
  | Etype_kind_clash of kind * typ
  | Earity_clash of int * int
  | Estate_arity_clash of Ident.t * int * int
  | Estate_unbound of Ident.t
  | Estate_initial
  | Ekind_not_combinatorial
  | Ekind_clash of kind * kind
  | Esome_labels_are_missing
  | Eequation_is_missing of Ident.t
  | Eglobal_is_a_function of Lident.t
  | Eapplication_of_non_function
  | Epattern_not_total
  | Econstr_arity of Lident.t * int * int							 
exception Error of Location.t * error
				
let error loc kind = raise (Error(loc, kind))

type warning =
  | Wpartial_matching of Zelus.pattern
  | Wunreachable_state of Ident.t
  | Wmatch_unused of Zelus.pattern
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
                        
let kind_message kind =
  match kind with
  | Tfun -> "function" 
  | Tnode -> "node"
  | Tstatic -> "static"
  		
let message loc kind =
  begin match kind with
  | Evar_undefined(name) ->
     eprintf "@[%aTyping error: The value identifier %s is unbound.@.@]"
             output_location loc (Ident.source name)
  | Emissing(s) ->
     eprintf "@[%aType error: no equation is given for name %s.@.@]"
        output_location loc
        (Ident.source s);
  | Eglobal_undefined(k, lname) ->
          eprintf "@[%aType error: the global value identifier %s %s is unbound.@.@]"
            output_location loc (kind_of_global_ident k)
            (Lident.modname lname)
  | Eglobal_already(k, s) ->
      eprintf "@[%aType error: the %s name %s is already defined.@.@]"
        output_location loc (kind_of_global_ident k) s 
  | Ealready(k, s) ->
     let k = kind_of_ident k in
     eprintf
       "@[%aType error: the identifier %s is defined twice with kind %s \
        in a parallel branch.@.@]"
        output_location loc (Ident.source s) k
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
      eprintf "@[%aType error: %s is a value of type %a,@ \
               but is expected to be a signal @,\
               (maybe a default value or initialization is missing).@.@]"
        output_location loc
        (Ident.source s)
	Ptypes.output expected_ty
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
        Ptypes.output actual_ty
        Ptypes.output expected_ty
  | Etype_kind_clash(k, actual_ty) ->
      eprintf "@[%aType error: this expression has type@ %a,@ \
               which does not belong to the %s kind.@.@]"
        output_location loc
        Ptypes.output actual_ty
        (kind_message k)
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
  | Ekind_not_combinatorial ->
      eprintf
        "@[%aType error: this expression should be combinatorial.@.@]"
        output_location loc
 | Ekind_clash(actual_kind, expected_kind) ->
       eprintf
        "@[%aType error: this is a %s expression and is expected to be %s.@.@]"
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
 | Econstr_arity(ln, expected_arity, actual_arity) ->
     eprintf
       "@[%aType error: the type constructor %a expects %d argument(s),@ \
        but is here given %d arguments(s).\n"
       output_location loc
       Printer.longname ln
       expected_arity
       actual_arity
  end;
  raise Misc.Error

    
let warning loc w =
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
 
