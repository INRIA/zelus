(***********************************************************************)
(*                                                                     *)
(*                                                                     *)
(*          Zelus, a synchronous language for hybrid systems           *)
(*                                                                     *)
(*  (c) 2024 Inria Paris (see the AUTHORS file)                        *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

(* variable creation *)
(* generating names *)
class name_generator =
  object
    val mutable counter = 0
    method name =
      counter <- counter + 1;
      counter
    method reset =
      counter <- 0
    method init i =
      counter <- i
  end

let symbol = new name_generator

(* association table with memoization *)
class name_assoc_table f =
  object
    val mutable counter = 0
    val mutable assoc_table: (int * string) list = []
    method name var =
      try
        List.assq var assoc_table
      with
        not_found ->
          let n = f counter in
          counter <- counter + 1;
          assoc_table <- (var,n) :: assoc_table;
          n
    method reset =
      counter <- 0;
      assoc_table <- []
  end

(* converting integers into variable names *)
(* variables are printed 'a, 'b *)
let int_to_letter bound i =
  if i < 26
  then String.make 1 (Char.chr (i+bound))
  else String.make 1 (Char.chr ((i mod 26) + bound)) ^ string_of_int (i/26)

let int_to_alpha i = int_to_letter 97 i
