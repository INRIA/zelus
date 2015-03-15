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
open Ident
open Format
open Pp_tools
open Lmm

let longname = Printer.longname
let immediate = Printer.immediate
let name = Printer.name
let ptype = Printer.ptype
	      
let rec pattern ff = function
  | Evarpat(n) -> name ff n
  | Etuplepat(pat_list) ->
      fprintf ff "@[<2>(%a)@]" (print_list_r pattern """,""") pat_list

let pkind ff = function
  | Estatic -> fprintf ff "const " | Evar -> fprintf ff "var "

let var_dec ff { p_kind = k; p_name = n; p_typ = typ } =
  fprintf ff "%s%a : %a" pkind k name ff n ptype typ

let var_dec_list ff = function
  | [] -> ()
  | l -> fprintf ff "@[<4>%a@]@\n" (print_list_r var_dec """;""") l

let rec expression ff { e_desc = desc } =
  match desc with
  | Elocal(n) -> name ff n
  | Eglobal(ln) -> longname ff ln
  | Econst(i) -> immediate ff i
  | Econstr0(g) -> lname ff ln
  | Eapp(op, e_list) -> operator op ff e_list
  | Erecord_access(e, ln) ->
     fprintf ff "@[%a.%a@]" expression e longname field
  | Erecord(l_e_list) ->
     print_record (print_couple longname expression """ =""") ff ln_e_list

let equation ff { eq_lhs = p; eq_rhs = e } =
  fprintf ff "@[%a = %a@]"
	  pattern p expression e

let equation_list ff = function
  | [] -> ()
  | l -> fprintf ff "@[<v2>let@ %a@]@\ntel" (print_list_r equation """;""") l

let fundecl ff n { f_kind = k; f_inputs = inputs; f_outputs = outputs;
		   f_local = locals; f_body = eq_list; f_assert = exp_opt } =
  fprintf ff "@[node %a%a%a@ returns %a@]@\n%a%a%a@]@\n@."
    print_qualname n
    print_node_params params
    print_vd_tuple ni
    print_vd_tuple no
    (print_opt print_contract) contract
    print_local_vars nl
    print_eqs ne

let implementation ff { desc = desc } =
  match desc with
  | Econstdecl(n, e) -> fprint ff "@[const %a = %a@]\n@." name n expression e
  | Efundecl(n, f) -> fundecl ff n f
  | Etypedecl(n, typ_decl) -> typedecl ff n typ_decl

let implementation_list ff imp_list =
  List.iter (implementation ff) imp_list
