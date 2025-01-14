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

(* a decision algorithm for equality between sizes; it is very basic *)
(* sizes are of the form:  s ::= s + s | s * s | xi | v *)

(* normal form: some of products *)

open Ident
open Deftypes

exception Equal

(* a monomial is an ordered product x0^i0 x1^i1 ... xn^in *)
(* it is represented as a map between variable and their power *)
module Product =
  Map.Make
    (struct
      type t = Ident.t * int
      let compare (id1, n1) (id2, n2) = Stdlib.compare (id1, n1) (id2, n2)
    end)

(* a multi-variate polynomial is an ordered sum of products [ci pi] *)
(* [c0 p0 + ... + cn pn] where [ci] is an integer and [pi] a product *)
module SumProduct =
  Map.Make
    (struct
      type t = int Product.t
      let compare (sp1: t) (sp2: t) =
        Product.compare Stdlib.compare sp1 sp2
    end)

(* Given a polynomial, compute its normal form *)
let sum sp1 sp2 =
  let p_list1 = SumProduct.to_list sp1 in
  List.fold_left sum_monomial p 
(* An alternative representation. Suppose that variables are ordered x0 < ... < xn *)
(* represent the polynomial as a value of the inductive type *)
(* pi = xi.Pk + pj where j => k /\ i > k, with Pk a polynomial. It is the *)
(* result of the Euclidian division of pi by variable xi. *)

let syntactic_equal si1 si2 =
  let rec equal si1 si2 =
  match si1, si2 with
  | Sint i1, Sint i2 when i1 = i2 -> ()
  | Svar(n1), Svar(n2) when Ident.compare n1 n2 = 0 -> ()
  | Sop(op1, si11, si12), Sop(op2, si21, si22) when op1 = op2 ->
     equal si11 si21; equal si12 si22
  | Sfrac { num = s1; denom = d1 },
    Sfrac { num = s2; denom = d2 } when d1 = d2 ->
     equal s1 s2
  | _ -> raise Equal in
  equal si1 si2
