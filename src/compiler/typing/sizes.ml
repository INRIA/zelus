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

(* a decision algorithm for equality between sizes; very basic *)
(* sizes are of the form:  s ::= s + s | s * s | xi | v *)

open Ident
open Deftypes

exception Equal

(* syntactic equatity *)
let syntactic_equality si1 si2 =
  let rec equal si1 si2 =
    match si1, si2 with
    | Sint i1, Sint i2 -> i1 = i2
    | Svar(n1), Svar(n2) -> n1 = n2
    | Sop(op1, si11, si12), Sop(op2, si21, si22) ->
       (op1 = op2) && (equal si11 si21) && (equal si12 si22)
    | Sfrac { num = s1; denom = d1 },
      Sfrac { num = s2; denom = d2 } -> (d1 = d2) && (equal s1 s2)
    | _ -> false in
  equal si1 si2

module type SIZE =
  sig
    type t
    val sum : t -> t -> t
    val prod : t -> t -> t
    val coef : int -> t -> t
    val zero : t -> bool
  end

(* normal form: some of products *)
module SumOfMonomials =
  struct
    (* a monomial [m] is an ordered product [x0^i0 x1^i1 ... xn^in] *)
    (* it is represented as a map : variable -> power *)
    module Product =
      Map.Make
        (struct
          type t = Ident.t
          let compare = Stdlib.compare
        end)

    type monomial = int Product.t

    let one = Product.empty
    let is_one m = Product.is_empty m
    let update p = function
      | None -> Some(p)
      | Some(p0) -> let p = p+p0 in if p = 0 then None else Some(p)
    let mult_x x i m = Product.update x (update i) m
    let mult m1 m2 = Product.fold mult_x m1 m2
    
    (* a multi-variate polynomial [sp] is an ordered sum of products [p . mi] *)
    (* [p0 . m0 + ... + pn . mn] where [pi] is an integer and [mi] a monomial *)
    (* [sp] is represented as a map *)
    module SumProduct =
      Map.Make
        (struct
          type t = int Product.t
          let compare = Product.compare Stdlib.compare
        end)
    
    type polynomial = int SumProduct.t

    let zero = SumProduct.empty
    let is_zero sp = SumProduct.is_empty sp
    
    let sum_m m p sp = SumProduct.update m (update p) sp
    let sum sp1 sp2 = SumProduct.fold sum_m sp1 sp2

    let mult_m m p sp =
      SumProduct.fold
        (fun m0 p0 sp0 -> sum_m (mult m m0) (p+p0) sp0) zero sp
    let mult sp1 sp2 = SumProduct.fold mult_m sp1 sp2
  end

(* An alternative representation. *)
(* Suppose that variables are ordered x0 < ... < xn *)
(* represent the polynomial as a value of the inductive type *)
(* pi = xi.Pk + pj where j => k /\ i > k, with Pk a polynomial. It is the *)
(* result of the Euclidian division of pi by variable xi. *)
