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

(* a decision algorithm for equality/inequalities between sizes *)
(* sizes are of the form:  s ::= s + s | s * s | xi | v | xi/v *)
open Ident
open Defsizes

exception Fail


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

        let minus sp1 sp2 = sum sp1 (mult (const (-1)) sp2)

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
      end

    (* a size expression is : s ::= s + s | s - s | s * s | xi | v | s / v *)
    (* the result of / is represented by fresh variables such that *)
    (* s / k = p with k * p + r = s with 0 <= r < k *)
    module Sizes =
      struct
        (* sets of equalities *)
        module S =
          Set.Make
            (struct type t = SumProduct.t let compare = SumProduct.compare end)
        (* a map : [(s, k) -> p, r] *)
        module Table =
          Map.Make
            (struct type t = SumProduct.t * int
                    let compare (sp1, k1) (sp2, k2) =
                      let v = SumProduct.compare sp1 sp2 in
                      if v = 0 then Stdlib.compare k1 k2 else v
             end)
        (* s with P1(x1,...,) = 0 /\ ... /\ P(x1 >= 0 /\ ... *)
        type t =
          { sp: SumProduct.t; (* a polynomal = sum of products *)
            eqs: S.t; (* a set of polynomials that are equal to zero *)
          }
                
        (* from explicit to implicit *)
        let rec make table si =
          let open SumProduct in
          match si with
          | Sint(i) -> const i, table
          | Svar(x) -> var x, table
          | Sop(Splus, si1, si2) ->
             let e1, table = make table si1 in
             let e2, table = make table si2 in
             sum e1 e2, table
          | Sop(Sminus, si1, si2) ->
             let e1, table = make table si1 in
             let e2, table = make table si2 in
             minus e1 e2, table
          | Sop(Smult, si1, si2) ->
             let e1, table = make table si1 in
             let e2, table = make table si2 in
             mult e1 e2, table
          | Sfrac { num; denom } ->
             let e, table = make table num in
             (* add entry [(e, denom) -> p, r] with [p], [r] fresh variables] *)
             (* if the entry does not exist already *)
             try
               let p, r = Table.find (e, denom) table in
               var p, table
             with
             | Not_found ->
                let p = Ident.fresh "n" in
                let r = Ident.fresh "n" in
                var p, Table.add (e, denom) (p, r) table

        let make si =
          let open SumProduct in
          let sp, table = make Table.empty si in
          let eqs =
            Table.fold
              (fun (sp, k) (p, r) acc ->
                (* sp = k * p + r *)
                S.add (minus sp (sum (var p) (var r))) acc) table S.empty in
          { sp; eqs }

        (* for the moment, we do not exploit equality constraints [eqs] *)
        let zero { sp } = SumProduct.is_zero sp
        let positive { sp } = SumProduct.positive sp
      end
  end

(* main entries *)
let zero = Sint 0
let one = Sint 1
let plus si1 si2 = Sop(Splus, si1, si2)
let minus si1 si2 = Sop(Sminus, si1, si2)
let mult si1 si2 = Sop(Smult, si1, si2)

type cmp = Eq | Lt | Lte

let norm si =
  let open SumOfProducts in
  let { Sizes.sp } = Sizes.make si in
  SumProduct.explicit sp

(* decisions *)
let compare cmp si1 si2 =
  let open SumOfProducts in
  match cmp with
  | Eq -> Sizes.zero (Sizes.make (minus si1 si2))
  (* si1 < si2, that is, si1 + 1 <= si2, that is, si2 - (si1 + 1) *)
  | Lt -> SumOfProducts.Sizes.positive (Sizes.make (minus si2 (plus si1 one)))
  | Lte ->
     SumOfProducts.Sizes.positive (Sizes.make (minus si2 si1))

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

(* evaluation of sizes *)
let rec eval env si =
  match si with
  | Sint(i) -> i
  | Sfrac { num; denom} ->
      let v = eval env num in
      v / denom
  | Svar(x) ->
      let v =
        try Env.find x env with Not_found -> raise Fail in v
  | Sop(op, si1, si2) ->
     let v1 = eval env si1 in
     let v2 = eval env si2 in
     let op = match op with | Splus -> (+) | Smult -> ( * ) | Sminus -> (-) in
     op v1 v2

(* evaluation of constraints *)
let rec trivial env sc =
  match sc with
  | Empty -> true
  | Rel { rel; lhs; rhs } ->
     let v1 = eval env lhs in
     let v2 = eval env rhs in
     let op = match rel with | Eq -> (=) | Lt -> (<=) | Lte -> (<=) in
     op v1 v2
  | And(sc_list) -> List.for_all (trivial env) sc_list
  | Let(id_e_list, sc) ->
     let env =
       List.fold_left
         (fun acc (id, s) -> Env.add id (eval env s) acc) env id_e_list in
     trivial env sc

(* free variables *)
let rec fv bounded acc si =
  match si with
  | Sint _ -> acc
  | Svar(n) -> if S.mem n bounded || S.mem n acc then acc else S.add n acc
  | Sfrac { num } -> fv bounded acc num
  | Sop(_, si1, si2) -> fv bounded (fv bounded acc si1) si2

let rec fv_constraints bounded acc sc =
  match sc with
  | Empty -> acc
  | And(sc_list) -> List.fold_left (fv_constraints bounded) acc sc_list
  | Rel { lhs; rhs } -> fv bounded (fv bounded acc lhs) rhs
  | Let(id_e_list, sc) ->
     let acc =
       List.fold_left (fun acc (_, s) -> fv bounded acc s) acc id_e_list in
     let bounded =
       List.fold_left (fun acc (id, _) -> S.add id bounded) bounded id_e_list in
     fv_constraints bounded acc sc

let apply op si1 si2 =
  match si1, si2 with
  | Sint(v1), Sint(v2) ->
     let op = match op with | Splus -> (+) | Sminus -> (-) | Smult -> ( * ) in
     Sint(op v1 v2)
  | _ -> Sop(op, si1, si2)

let frac num denom =
  match num with | Sint(vi) -> Sint(vi / denom) | _ -> Sfrac { num; denom }

let rec subst env si =
  match si with
  | Sint _ -> si
  | Sop(op, si1, si2) -> apply op si1 si2
  | Sfrac { num; denom } -> frac (subst env num) denom
  | Svar(n) ->
     try Env.find n env with | Not_found -> raise Fail

let subst_in_constraints env sc =
  if Env.is_empty env then sc
  else
    let id_e_list = Env.fold (fun id e acc -> (id, e) :: acc) env [] in
    Let(id_e_list, sc)
 
(* An alternative representation. *)
(* Suppose that variables are ordered x0 < ... < xn *)
(* represent the polynomial as a value of the inductive type *)
(* pi = xi.pk + pj where j => k /\ i > k, with Pk a polynomial. It is the *)
(* result of the Euclidian division of pi by variable xi. *)

