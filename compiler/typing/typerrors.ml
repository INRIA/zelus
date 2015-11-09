(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2014                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
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

type kind_of_ident = Current | Initial | Derivative | CurrentDerivative

type error =
    | Emissing of Ident.t
    | Eglobal_undefined of kind_of_global_ident * Lident.t
    | Eglobal_already of kind_of_global_ident * string
    | Ealready of kind_of_ident * Ident.t
    | Eis_a_value of Ident.t
    | Einit_undefined of Ident.t
    | Elast_undefined of Ident.t
    | Eshould_be_a_signal of Ident.t * typ
    | Ecannot_be_set of bool * Ident.t
    | Etype_clash of typ * typ
    | Earity_clash of int * int
    | Estate_arity_clash of Ident.t * int * int
    | Estate_unbound of Ident.t
    | Estate_initial
    | Ekind_not_combinatorial
    | Ekind_clash of kind * kind
    | Esome_labels_are_missing
    | Eequation_is_missing of Ident.t
    | Eglobal_is_a_function of Lident.t
    | Eapplication_of_non_function of Lident.t
    | Eperiod_not_positive of float
    | Ereset_target_state of bool * bool
    | Epattern_not_total
    | Ecombination_function of Ident.t
			      
exception Error of location * error

let error loc kind = raise (Error(loc, kind))

type warning =
  | Wpartial_matching of Zelus.pattern
  | Wunreachable_state of Ident.t
  | Wmatch_unused of Zelus.pattern
  | Wequation_does_not_define_a_name
  		       
let kind_of_global_ident k = match k with
    | Value -> "value" | Type -> "type" 
    | Constr -> "constructor" | Label -> "label"

let kind_of_ident k =
  match k with
  | Current -> "value", ""
  | Derivative -> "derivative", ""
  | Initial -> "initial value", ""
  | CurrentDerivative ->
     "value", " (a value and its derivative must occur in exclusive branches)"
		
let message loc kind =
  begin match kind with
  | Emissing(s) ->
      eprintf "%aType error: no equation is given for name %s.@."
        output_location loc
        (Ident.source s);
  | Eglobal_undefined(k, lname) ->
          eprintf "%aThe %s name %s is unbound (may need a 'rec').@."
            output_location loc (kind_of_global_ident k)
            (Lident.modname lname)
  | Eglobal_already(k, s) ->
      eprintf "%aType error: the %s name %s is already defined.@."
        output_location loc (kind_of_global_ident k) s 
  | Ealready(k, s) ->
     let prefix, suffix = kind_of_ident k in
     eprintf "%aType error: the %s of %s is defined twice%s.@."
        output_location loc prefix (Ident.source s) suffix
  | Einit_undefined(s) ->
      eprintf "%aType error: %s must be initialized in every branch.@."
        output_location loc
        (Ident.source s)
  | Eis_a_value(s) ->
      eprintf "%aType error: last %s is forbidden as %s is a value.@."
        output_location loc
        (Ident.source s) (Ident.source s)
  | Elast_undefined(s) ->
      eprintf "%aType error: %s is not a state variable so last %s is \
              forbidden.@."
        output_location loc
        (Ident.source s) (Ident.source s)
  | Eshould_be_a_signal(s, expected_ty) ->
      eprintf "@[%aType error: %s is a value of type %a,@ \
               but is expected to be a signal \
               (maybe a default or initialization is missing).@.@]"
        output_location loc
        (Ident.source s)
	Ptypes.output expected_ty
  | Ecannot_be_set(is_next, s) ->
      eprintf "%aType error: the %s value of %s cannot be set. This is either \
               because the %s value is set or the last value is used.@."
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
  | Earity_clash(actual_arit, expected_arit) ->
      eprintf "%aType error: the operator expects %d arguments,@ \
               but is given %d arguments.@."
        output_location loc
        expected_arit actual_arit
  | Estate_arity_clash(name, actual_arit, expected_arit) ->
      eprintf "%aType error: the state %s expects %d arguments,@ \
               but is given %d arguments.@."
        output_location loc
        (Ident.source name)
        expected_arit actual_arit
  | Estate_unbound(name) ->
      eprintf
        "%aType error: the state %s is unbound in the current automaton.@."
        output_location loc
        (Ident.source name)
  | Estate_initial ->
      eprintf
        "%aType error: the initial state cannot be parameterized.@."
        output_location loc
  | Ekind_not_combinatorial ->
      eprintf
        "%aType error: this expression should be combinatorial.@."
        output_location loc
 | Ekind_clash(actual_kind, expected_kind) ->
      let message kind =
        match kind with
          | Tcont -> "continuous"
          | Tany -> "combinatorial"
          | Tdiscrete(s) -> if s then "discrete" else "stateless discrete" in
      eprintf
        "%aType error: this is a %s expression and is expected to be %s.@."
        output_location loc
        (message actual_kind) (message expected_kind)
 | Esome_labels_are_missing ->
      eprintf
        "%aType error: some fields are missing.@."
        output_location loc
 | Eequation_is_missing(name) ->
     eprintf
       "%aType error: the variable %s must be defined in an equation.@."
       output_location loc
       (Ident.source name)
 | Eglobal_is_a_function(lname) ->
     eprintf "%aType error: the global name %s must not be a function.@."
        output_location loc
        (Lident.modname lname)
 | Eapplication_of_non_function(lname) ->
     eprintf "%aType error: the global name %s is not a function.@."
        output_location loc
        (Lident.modname lname)
 | Eperiod_not_positive(f) ->
     eprintf 
       "%aType error: the period contains %f which is not strictly positive.@."
       output_location loc f
 | Ereset_target_state(actual_reset, expected_reset) ->
     eprintf
       "%aType error: the target state is expected to be %s by is entered by %s.@."
       output_location loc
       (if expected_reset then "reset" else "on history")
       (if actual_reset then "reset" else "history")
 | Epattern_not_total ->
     eprintf
       "%aType error: this pattern must be total.@."
       output_location loc
 | Ecombination_function(n) ->
     eprintf
       "%aType error: a combination function for %s must be given.@."
       output_location loc (Ident.source n)
  end;
  raise Misc.Error

let warning loc w =
  match w with
  | Wpartial_matching(p) ->
     Format.eprintf "%aType warning: this pattern-matching is not exhaustive.\n"
		    output_location loc;
     Format.eprintf "Here is an example of a value that is not matched:\n%a\n"
		    Printer.pattern p
  | Wunreachable_state(s) ->
     eprintf
       "%aType warning: the state %s in this automaton is unreachable.@."
       output_location loc
       (Ident.source s)
  | Wmatch_unused(p) ->
     Format.eprintf "Type warning: match case \"%a\" is unused.\n" Printer.pattern p
  | Wequation_does_not_define_a_name ->
     eprintf
       "%aType warning: this equation does not define a name.\n\
          The compiler may consider it as deadcode and remove it.@."
       output_location loc
     
