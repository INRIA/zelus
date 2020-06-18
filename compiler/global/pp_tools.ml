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

(* useful stuff for printing *)

open Format

let print_if_not_empty print ff = function | [] -> () | l -> print ff l
								   
let print_list_no_space print po sep pf ff l =
  let rec printrec ff l =
    match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l ->
       fprintf ff "@[%a%s%a@]" print x sep printrec l in
  fprintf ff "@[%s%a%s@]" po printrec l pf

(* prints [po body [sep body]+ pf] *)
let print_list_r print po sep pf ff l =
  let rec printrec ff l =
    match l with
    | [] -> ()
    | [x] -> print ff x
    | x :: l ->
       fprintf ff "@[<hov>%a@ %s@ @[%a@]@]" print x sep printrec l in
  fprintf ff "@[%s%a%s@]" po printrec l pf

(* prints in a row a [po body [sep body]+ pf] *)
let print_list_l print po sep pf ff l =
  let rec printrec ff l =
    match l with
    | [] -> ()
    | x :: l -> fprintf ff "@[%s%a@ %a@]" sep print x printrec l in
  match l with
  | [] -> fprintf ff "%s%s" po pf
  | [x] -> fprintf ff "%s%a%s" po print x pf
  | x :: l -> fprintf ff "@[<hov 0>%s%a@ %a%s@]" po print x printrec l pf


let print_list_r_empty print po sep pf ff l =
  print_if_not_empty (print_list_r print po sep pf) ff l


let print_couple print1 print2 po sep pf ff (c1, c2) =
  fprintf ff "@[<hov>%s@[%a@]%s@ @[%a@]%s@]" po print1 c1 sep print2 c2 pf

let print_couple2 print1 print2 po sep1 sep2 pf ff (c1, c2) =
  fprintf ff
	  "@[<hov>%s@[%a@]%s@ %s@[%a@]%s@]" po print1 c1 sep1 sep2 print2 c2 pf

let print_record print ff r =
  fprintf ff "@[<hv2>%a@]" (print_list_r print "{ "";"" }") r

let print_with_braces print po pf ff p = fprintf ff "@[%s%a%s@]" po print p pf

let print_opt print ff = function
  | None -> ()
  | Some(s) -> print ff s

let print_opt2 print sep ff = function
  | None -> ()
  | Some(s) -> fprintf ff "@[%s%a@]" sep print s
