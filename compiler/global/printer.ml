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

(* the printer *)

open Location
open Misc
open Zelus
open Deftypes
open Ptypes
open Global
open Modules
open Pp_tools
open Format

(* Infix chars are surrounded by parenthesis *)
let is_infix =
  let module StrSet = Set.Make(String) in
  let set_infix =
    List.fold_right
      StrSet.add
      ["or"; "quo"; "mod"; "land"; "lor"; "lxor"; "lsl"; "lsr"; "asr"]
      StrSet.empty in
    fun s -> StrSet.mem s set_infix

let parenthesis s =
  let c = String.get s 0 in
  if is_infix s then "(" ^ s ^ ")"
  else match c with
    | 'a' .. 'z' | 'A' .. 'Z' | '_' | '`' -> s
    | '*' -> "( " ^ s ^ " )"
    | _ -> if s = "()" then s else "(" ^ s ^ ")"

let shortname ff s = fprintf ff "%s" (parenthesis s)

let qualident ff { Lident.qual = m; Lident.id = s } =
  fprintf ff "%s.%s" m (parenthesis s)

let longname ff ln =
  let ln = Initial.short (currentname ln) in
  match ln with
    | Lident.Name(m) -> shortname ff m
    | Lident.Modname(qual) -> qualident ff qual

let name ff n = shortname ff (Ident.name n)

let source_name ff n = shortname ff (Ident.source n)

let immediate ff = function
  | Eint i -> fprintf ff "%d" i
  | Efloat f -> fprintf ff "%f" f
  | Ebool b -> if b then fprintf ff "true" else fprintf ff "false"
  | Estring s -> fprintf ff "%S" s
  | Echar c -> fprintf ff "'%c'" c
  | Evoid -> fprintf ff "()"

let rec ptype ff { desc } =
  match desc with
  | Etypevar(s) -> fprintf ff "'%s" s
  | Etypeconstr(ln, ty_list) ->
     fprintf ff "@[<hov2>%a@]%a"
       (print_list_r_empty ptype "("","")") ty_list
       longname ln
  | Etypetuple(ty_list) ->
     fprintf ff "@[<hov2>%a@]" (print_list_r ptype "(""*"")") ty_list
  | Etypefun(k, ty_arg, ty_res) ->
     let s = match k with | Kfun -> "->" | Knode -> "=>" | Kstatic -> ">" in
     fprintf ff "@[<hov2>%a %s %a@]" ptype ty_arg s ptype ty_res

let rec pattern ff { pat_desc } =
  match pat_desc with
  | Evarpat(n) -> fprintf ff "%a" name n
  | Ewildpat -> fprintf ff "_"
  | Econstpat(im) -> immediate ff im
  | Econstr0pat(ln) -> longname ff ln
  | Econstr1pat(ln, pat_list) ->
     fprintf ff "@[%a%a@]" longname ln (pattern_list "(" "," ")") pat_list
  | Etuplepat(pat_list) -> pattern_list "(" "," ")" ff pat_list
  | Etypeconstraintpat(p, ty_exp) ->
     fprintf ff "@[(%a:%a)@]" pattern p ptype ty_exp
  | Erecordpat(n_pat_list) ->
     print_record (print_couple longname pattern """ =""") ff n_pat_list
  | Ealiaspat(p, n) ->
     fprintf ff "%a as %a" pattern p name n
  | Eorpat(pat1, pat2) ->
     fprintf ff "%a | %a" pattern pat1 pattern pat2

and pattern_list po sep pf ff pat_list =
  fprintf ff "@[%a@]" (print_list_r pattern po sep pf) pat_list

