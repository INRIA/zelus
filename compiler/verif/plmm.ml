(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2020 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* Printer for lmm *)

open Location
open Format
open Pp_tools
open Ident
open Lident
open Lmm

let longname = Printer.longname
let name = Printer.name
let shortname = Printer.shortname

let immediate ff = function
  | Lint i -> fprintf ff "%d" i
  | Lfloat f -> fprintf ff "%f" f
  | Lbool b -> if b then fprintf ff "true" else fprintf ff "false"
  | Lstring s -> fprintf ff "%S" s
  | Lchar c -> fprintf ff "'%c'" c
  | Lvoid -> fprintf ff "()"

let constr0pat ff = function
  | Lboolpat(b) -> fprintf ff "%s" (if b then "true" else "false")
  | Lconstr0pat(ln) -> longname ff ln

let rec expression ff e =
  match e with
  | Llocal(n) -> name ff n
  | Llast(n) -> fprintf ff "@[(last %a)@]" name n
  | Lglobal(ln) -> longname ff ln
  | Lconst(i) -> immediate ff i
  | Lconstr0(ln) -> longname ff ln
  | Lapp(op, e_list) ->
      fprintf ff "@[(%a %a)@]" operator op expression_list e_list
  | Lrecord_access(e, ln) -> fprintf ff "@[%a.%a@]" expression e longname ln
  | Lrecord(ln_e_list) ->
      let handler ff (ln, e) =
        fprintf ff "@[%a %a@]" longname ln expression e in
      fprintf ff "@[(record@ %a)@]" (print_list_r handler "" "" "") ln_e_list
  | Ltuple(e_list) ->
      fprintf ff "@[(tuple@ %a)@]" (print_list_r expression "" "" "") e_list
  | Lget(e, i) ->
      fprintf ff "@[(get@ %a %d)@]" expression e i
  | Lmerge(e, ln_e_list) ->
      let handler ff (cpat, e) =
        fprintf ff "@[%a %a@]" constr0pat cpat expression e in
      fprintf ff "@[(merge@ %a@ %a)@]" expression e
	(print_list_r handler "" "" "") ln_e_list
  | Lwhen(e1, cpat, e2) ->
      fprintf ff
        "@[(when@ %a@ %a(%a)@]" expression e1 constr0pat cpat expression e2
 
and expression_list ff e_list = print_list_r expression "" " " "" ff e_list
    
and kind ff k =
  match k with
  | Def -> fprintf ff "def"
  | Init(r) -> fprintf ff "init%a" reset_opt r
  | Next -> fprintf ff "next"

and reset ff r =
  match r with
  | Res_never -> fprintf ff "false"
  | Res_else(r, e) -> fprintf ff "@[(else %a %a)@]" reset r expression e

and reset_opt ff r =
  match r with
  | Res_never -> ()
  | Res_else(Res_never, e) -> fprintf ff "@[(%a)@]" expression e
  | Res_else(r, e) -> fprintf ff "@[(%a || %a)@]" reset_opt r expression e

and clock ff ck =
  match ck with
  | Ck_base -> fprintf ff "true"
  | Ck_on(ck, cpat, e) ->
      fprintf ff "@[(on %a %a(%a))@]" clock ck constr0pat cpat expression e
  
and clock_opt ff ck =
  match ck with
  | Ck_base -> () | _ -> fprintf ff "@[ on %a@]" clock ck

and operator ff op =
  match op with
  | Lunarypre -> fprintf ff "pre"
  | Lfby -> fprintf ff "fby"
  | Lminusgreater -> fprintf ff "->"
  | Lifthenelse -> fprintf ff "if"
  | Lsharp -> fprintf ff "#"
  | Lop(ln) -> longname ff ln

let equation ff { eq_kind = k; eq_ident = x; eq_exp = e; eq_clock = ck } =
  fprintf ff "@[(%a %a = %a%a)@]" kind k name x expression e clock_opt ck

let rec ptype ff ty =
  match ty with
  | Tint -> fprintf ff "int"
  | Tbool -> fprintf ff "bool"
  | Tfloat -> fprintf ff "float"
  | Tunit -> fprintf ff "unit"
  | Tchar -> fprintf ff "char"
  | Tstring -> fprintf ff "string"
  | Tconstr(qualid) -> Ptypes.print_qualid ff qualid
  | Tproduct(ty_list) -> Pp_tools.print_list_r ptype "(" " * " ")" ff ty_list
                           
let print_env ff env =
  print_list_r
    (fun ff (n,{ t_typ = ty }) -> fprintf ff "@[(%a %a)@]" name n ptype ty)
    "(environment " "" ")" ff (Env.bindings env)

let fundecl ff n { f_inputs = inputs; f_output = output;
                   f_env = env; f_body = eq_list; f_assert = e_list } =
  fprintf ff "@[<v2>(property %s%a(%a)@,@[<v1>(%a@,%a@,%a))@]@]"
    n
    (print_list_l name "(" " " ")") inputs
    name output
    print_env env
    (print_list_l expression "(assert " " " ")") e_list
    (print_list_l equation "(equation " " " ")") eq_list

let type_decl ff ty_decl =
  match ty_decl with
    | Labstract_type -> ()
    | Lvariant_type(tag_name_list) ->
        fprintf ff "@[(sum %a)@]" (print_list_l shortname "" " " "") tag_name_list
    | Lrecord_type(n_ty_list) ->
       let handler ff (n, ty) =
	 fprintf ff "@[%a %a@]" shortname n ptype ty in
       fprintf ff "@[(record %a)@]" (print_list_l handler "" "" "") n_ty_list

let implementation ff impl =
  match impl with
  | Lconstdecl(n, e) -> fprintf ff "@[(const %s %a)@]\n@." n expression e
  | Lfundecl(n, f) -> fundecl ff n f
  | Ltypedecl(n, ty_decl) ->
     fprintf ff "@[<v 2>(type %s@, %a)@.@]" n type_decl ty_decl

let implementation_list ff imp_list =
  print_list_l implementation "" " " "" ff imp_list
    
