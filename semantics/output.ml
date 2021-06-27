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

open Lident
open Value

let lident ff lid =
  match lid with
  | Name(s) -> Format.fprintf ff "%s" s
  | Modname { qual; id } -> Format.fprintf ff "%s.%s" qual id
                          
let rec value_list value ff l =
  match l with
  | [] -> assert false
  | [x] -> value ff x
  | x :: l -> Format.printf "@[%a,@ %a@]" value x (value_list value) l
            
let rec pvalue ff v =
  match v with
  | Vint(i) -> Format.fprintf ff "%i" i
  | Vbool(b) -> Format.fprintf ff "%s" (if b then "true" else "false")
  | Vfloat(f) -> Format.fprintf ff "%f" f
  | Vchar(c) -> Format.fprintf ff "%c" c
  | Vstring(s) -> Format.fprintf ff "%s" s
  | Vvoid -> Format.fprintf ff "()"
  | Vtuple(l) ->
     Format.fprintf ff "@[<hov 1>(%a)@]" (value_list value) l
  | Vconstr0(lid) -> lident ff lid
  | Vconstr1(lid, l) ->
     Format.fprintf ff "@[<hov 1>%a(%a)@]" lident lid (value_list value) l 
  | Vstate0(id) -> Ident.fprint_t ff id
  | Vstate1(id, l) ->
     Format.fprintf
       ff "@[<hov 1>%a(%a)@]" Ident.fprint_t id (value_list value) l
    
and value ff v =
  match v with
  | Vnil -> Format.fprintf ff "nil"
  | Vbot -> Format.fprintf ff "bot"
  | Value(v) -> pvalue ff v                 
              
let pvalue_list ff l = value_list pvalue ff l
                     
let value_list ff l = value_list value ff l
                    
let value_and_flush ff v =
  Format.fprintf ff "%a@\n" value v
let value_list_and_flush ff l = 
  Format.fprintf ff "%a@\n" value_list l
let pvalue_list_and_flush ff l = 
  Format.fprintf ff "%a@\n" pvalue_list l
