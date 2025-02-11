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

(* a decision algorithm for equality between sizes; basic *)
(* sizes are of the form:  s ::= s + s | s * s | xi | v | xi div v | xi mod v *)

open Ident
open Defsizes

exception Equal

(* syntactic equatity *)
let syntactic_equal si1 si2 =
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

(* normal form: some of products *)
module SumOfProducts =
  struct
    (* a monomial [m] is an ordered product [x0^i0 x1^i1 ... xn^in] *)
    (* it is represented as a map : variable -> power *)
    let update p = function
      | None -> Some(p)
      | Some(p0) -> let p = p+p0 in if p = 0 then None else Some(p)

    module Product =
      struct
        module M =
          Map.Make (struct type t = Ident.t let compare = Stdlib.compare end)

        type t = int M.t

        let one = M.empty
        let is_one m = M.is_empty m
        let var x = M.singleton x 1
        let mult_x x i m = M.update x (update i) m
        let mult m1 m2 = M.fold mult_x m1 m2
        let compare = M.compare Stdlib.compare
        let equal s1 s2 = compare s1 s2 = 0
        
        (* explicit representation [x0^i0...xn^in] *)
        let explicit m =
          let v_list = M.to_list m in
          let mult s1 s2 =
            match s1 with | Sint(1) -> s2 | _ -> Sop(Smult, s1, s2) in
          let rec power x i =
            match i with
            | 0 -> assert false
            | 1 -> Svar(x) | _ -> Sop(Smult, Svar(x), power x (i-1)) in
          List.fold_left
            (fun acc (x, i) -> mult acc (power x i)) (Sint(1)) v_list
      end
    
    (* a multi-variate polynomial [sp] is an ordered sum of products [p . mi] *)
    (* [p0 . m0 + ... + pn . mn] where [pi] is an integer and [mi] a monomial *)
    (* [sp] is represented as a map *)
    module SumProduct =
      struct
        module M =
          Map.Make (struct type t = Product.t let compare = Product.compare end)
        type t = int M.t
        
        let zero = M.empty
        let is_zero sp = M.is_empty sp
        
        let const v = if v = 0 then zero else M.singleton Product.one v

        let var x = M.singleton (Product.var x) 1
        
        let sum_m m p sp = M.update m (update p) sp
        let sum sp1 sp2 = M.fold sum_m sp1 sp2
        
        let mult_m m p sp =
          M.fold (fun m0 p0 sp0 -> sum_m (Product.mult m m0) (p*p0) sp0) sp zero
        let mult sp1 sp2 = M.fold mult_m sp1 sp2

        let compare sp1 sp2 = M.compare Stdlib.compare sp1 sp2

        let equal sp1 sp2 = compare sp1 sp2 = 0

        (* positive - not complete *)
        let positive : _ -> bool = fun sp -> M.for_all (fun _ p -> p >= 0) sp
        
        (* explicit representation [p0 . m0 + ... + pn . mn] *)
        let explicit m =
          let v_list = M.to_list m in
          let sum s1 s2 =
            match s1 with | Sint(0) -> s2 | _ -> Sop(Splus, s1, s2) in
          let mult p m =
            match p with
            | 0 -> assert false | 1 -> m | _ -> Sop(Smult, Sint(p), m) in
          List.fold_left
            (fun acc (m, p) -> sum acc (mult p (Product.explicit m)))
            (Sint(0)) v_list

        (* from explicit to implicit *)
        let rec make si =
          match si with
          | Sint(i) -> const i
          | Svar(x) -> var x
          | Sop(Splus, si1, si2) -> sum (make si1) (make si2)
          | Sop(Sminus, si1, si2) ->
             sum (make si1) (mult (const (-1)) (make si2))
          | Sop(Smult, si1, si2) -> mult (make si1) (make si2)
          | _ -> assert false
      end
  end

(* main entries *)
open SumOfProducts.SumProduct

let zero = Sint 0
let one = Sint 1
let plus si1 si2 = Sop(Splus, si1, si2)
let minus si1 si2 = Sop(Sminus, si1, si2)
let mult si1 si2 = Sop(Smult, si1, si2)

type cmp = Eq | Lt | Lte

let norm si = explicit (make si)

(* decisions *)
let compare cmp si1 si2 =
  match cmp with
  | Eq -> equal (make si1) (make si2)
  (* si1 < si2, that is, si1 + 1 <= si2, that is, si2 - (si1 + 1) *)
  | Lt -> positive (make (minus si2 (plus si1 one)))
  | Lte -> positive (make (minus si2 si1))
  
(* An alternative representation. *)
(* Suppose that variables are ordered x0 < ... < xn *)
(* represent the polynomial as a value of the inductive type *)
(* pi = xi.pk + pj where j => k /\ i > k, with Pk a polynomial. It is the *)
(* result of the Euclidian division of pi by variable xi. *)

