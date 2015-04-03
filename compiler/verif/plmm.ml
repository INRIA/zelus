(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2015                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* Printer for lmm *)

open Location
open Format
open Pp_tools
open Lmm

let longname = Printer.longname
let immediate = Printer.immediate
let name = Printer.name
let shortname = Printer.shortname
let internal_type = Ptypes.output

let rec pattern ff = function
  | Evarpat(n) -> name ff n
  | Etuplepat(pat_list) ->
      fprintf ff "@[<2>(%a)@]" (print_list_r pattern """,""") pat_list

let pkind ff = function
  | Estatic -> fprintf ff "const " | Evar -> fprintf ff "var "

let var_dec ff { p_kind = k; p_name = n; p_typ = typ } =
  fprintf ff "%a%a : %a" pkind k name n internal_type typ

let var_dec_list ff = function
  | [] -> ()
  | l -> fprintf ff "@[<4>%a@]@\n" (print_list_r var_dec """;""") l

let rec expression ff { e_desc = desc } =
  match desc with
  | Elocal(n) -> name ff n
  | Eglobal(ln) -> longname ff ln
  | Econst(i) -> immediate ff i
  | Econstr0(ln) -> longname ff ln
  | Eapp(op, e_list) -> operator ff op e_list
  | Erecord_access(e, ln) -> fprintf ff "@[%a.%a@]" expression e longname ln
  | Erecord(ln_e_list) ->
    print_record (print_couple longname expression """ =""") ff ln_e_list
  | Etuple(e_list) ->
    fprintf ff "@[%a@]" (print_list_r expression "("", "")") e_list

and operator ff op e_list =
  match op, e_list with
  | Eunarypre, [e] ->
     fprintf ff "@[pre@ %a@]" expression e
  | Eminusgreater, [e1; e2] ->
     fprintf ff "@[%a ->@ %a@]" expression e1 expression e2
  | Eifthenelse, [e1; e2; e3] ->
     fprintf ff "@[<hov>if %a@ then %a@ else %a@]"
             expression e1 expression e2 expression e3
  | Eop(ln), e_list ->
     fprintf ff "@[%a%a@]" longname ln (print_list_r expression "("","")") e_list
  | _ -> assert false

let p_assert ff e =
  fprintf ff "@[assert@ %a;@]" expression e

let equation ff { eq_lhs = p; eq_rhs = e } =
  fprintf ff "@[%a = %a@]"
          pattern p expression e

let equation_list_with_assert e_opt ff = function
  | [] -> ()
  | l ->
     fprintf ff "@[<v2>let@ %a%a@]@\ntel"
             (print_opt p_assert) e_opt
             (print_list_r equation """;""") l

let fundecl ff n { f_kind = k; f_inputs = inputs; f_outputs = outputs;
                   f_local = locals; f_body = eq_list; f_assert = e_opt } =
  fprintf ff "@[node %s%a@ returns %a@]@\n%a%a@]@\n@."
    n
    var_dec_list inputs
    var_dec_list outputs
    var_dec_list locals
    (equation_list_with_assert e_opt) eq_list

let implementation ff { desc = desc } =
  match desc with
  | Econstdecl(n, e) -> fprintf ff "@[const %s = %a@]\n@." n expression e
  | Efundecl(n, f) -> fundecl ff n f
  | Etypedecl(n, params, ty_decl) ->
     fprintf ff "@[<v 2>type %a %s %a@.@]"
	     Pp_tools.print_type_params params n
	     Printer.type_decl ty_decl

let implementation_list ff imp_list =
  List.iter (implementation ff) imp_list
