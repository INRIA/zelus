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
exception Maybe of Defsizes.exp eq list

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
        let is_surely_zero sp = M.is_empty sp
        let is_surely_not_zero sp = 
          (* if [sp = p] with [p an integer] *)
          if M.cardinal sp = 1 then M.mem Product.one sp else false
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
        let is_surely_positive : _ -> bool = 
          fun sp -> M.for_all (fun _ p -> p >= 0) sp
        let is_surely_not_positive : _ -> bool = 
          fun sp -> M.for_all (fun _ p -> p < 0) sp
        
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

        (* implicit representation *)
        let rec make si =
          match si with
          | Sint(i) -> const i
          | Svar(x) -> var x
          | Sop(op, si1, si2) ->
             let e1 = make si1 in
             let e2 = make si2 in
             let op = 
               match op with Splus -> sum | Sminus -> minus | Smult -> mult in
             op e1 e2
          | Sfrac _ ->
             (* the term must have been normalized before *)
             assert false
      end
  end

(* main entries *)
let const v = Sint v
let zero = const 0
let one = const 1
let var x = Svar(x)
let plus si1 si2 = Sop(Splus, si1, si2)
let minus si1 si2 = Sop(Sminus, si1, si2)
let mult si1 si2 = Sop(Smult, si1, si2)

(* elimination of div (and later [mod]) operations in size expressions *)
let normalize si =
  let module Table =
    Map.Make
      (struct type t = Defsizes.exp * int let compare = Stdlib.compare end) in
  let rec simpl table si =
    match si with
    | Sint _ | Svar _ -> si, table
    | Sop(op, si1, si2) ->
       let si1, table = simpl table si1 in
       let si2, table = simpl table si2 in
       Sop(op, si1, si2), table
    | Sfrac { num; denom } ->
       let e, table = simpl table num in
       (* add entry [(e, denom) -> p, r] with [p], [r] fresh variables] *)
       (* if the entry does not exist already *)
       try
         let p, _ = Table.find (e, denom) table in
         Svar(p), table
       with
       | Not_found ->
          let p = Ident.fresh "n" in
          let r = Ident.fresh "r" in
          Svar(p), Table.add (e, denom) (p, r) table in
  let si, table = simpl Table.empty si in
  let eqs =
    Table.fold
      (fun (e, k) (p, r) acc ->
        (* [e/k is replaced by p with constraints] *)
        (* [e = k * p + r] /\ 0 <= e /\ 0 <= p /\ 0 <= r /\ r <= 1] *)
        { rel = Eq; lhs = e; rhs = plus (mult (const k) (var p)) (var r) } ::
           { rel = Lte; lhs = const 0; rhs = e } ::
             { rel = Lte; lhs = const 0; rhs = var p } ::
               { rel = Lte; lhs = const 0; rhs = var r } ::
                 { rel = Lte; lhs = var r; rhs = const 1 } :: acc)
      table [] in
  si, eqs

(* temporary solution *)
let norm si =
  let open SumOfProducts in
  let si, _ = normalize si in
  let e = SumProduct.make si in
  SumProduct.explicit e

(* decision *)
let compare cmp si1 si2 =
  try
    let result = match cmp with
      | Eq ->
         let si, eqs = normalize (minus si1 si2) in
         let open SumOfProducts.SumProduct in
         let sp = make si in
         if is_surely_zero sp then true
         else if is_surely_not_zero sp then false
         else raise (Maybe(eqs))
      | (* si1 < si2, that is, si1 + 1 <= si2, that is, si2 - (si1 + 1) *)
        Lt ->
         let si, eqs = normalize (minus si2 (plus si1 one)) in
         let open SumOfProducts.SumProduct in
         let sp = make si in
         if is_surely_positive sp then true
         else if is_surely_not_positive sp then false
         else raise (Maybe(eqs))
      | Lte ->
         let si, eqs = normalize (minus si2 si1) in
         let open SumOfProducts.SumProduct in
         let sp = make si in
         if is_surely_positive sp then true
         else if is_surely_not_positive sp then false
         else raise (Maybe(eqs)) in
    result
  with
  | Maybe(eqs) ->
     (* add it to the constraint environment *)
       Defsizes.add
          (And (Rel { rel = Lte; lhs = si1; rhs = si2 } ::  
                  List.map (fun eq -> Rel eq) eqs)); true

(* decision *)
let compare cmp si1 si2 =
  try
    let result = match cmp with
      | Eq ->
         let si, eqs = normalize (minus si1 si2) in
         let open SumOfProducts.SumProduct in
         let sp = make si in
         if is_surely_zero sp then true
         else if is_surely_not_zero sp then false
         else raise (Maybe(eqs))
      | (* si1 < si2, that is, si1 + 1 <= si2, that is, si2 - (si1 + 1) *)
        Lt ->
         let si, eqs = normalize (minus si2 (plus si1 one)) in
         let open SumOfProducts.SumProduct in
         let sp = make si in
         if is_surely_positive sp then true
         else if is_surely_not_positive sp then false
         else raise (Maybe(eqs))
      | Lte ->
         let si, eqs = normalize (minus si2 si1) in
         let open SumOfProducts.SumProduct in
         let sp = make si in
         if is_surely_positive sp then true
         else if is_surely_not_positive sp then false
         else raise (Maybe(eqs)) in
    result
  with
  | Maybe _ ->
     Defsizes.add (Rel { rel = cmp; lhs = si1; rhs = si2 }); true

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
let rec eval n_env si =
  match si with
  | Sint(i) -> i
  | Sfrac { num; denom} ->
      let v = eval n_env num in
      v / denom
  | Svar(x) ->
      let v =
        try Env.find x n_env with Not_found -> raise Fail in v
  | Sop(op, si1, si2) ->
     let v1 = eval n_env si1 in
     let v2 = eval n_env si2 in
     let op = match op with | Splus -> (+) | Smult -> ( * ) | Sminus -> (-) in
     op v1 v2

(* evaluation of constraints. *)
(* [f_env]: environment of functions; [n_env]: environment of sizes *)
let rec trivial f_env n_env sc =
  match sc with
  | True -> true
  | False -> false
  | Rel { rel; lhs; rhs } ->
     let v1 = eval n_env lhs in
     let v2 = eval n_env rhs in
     let op = match rel with | Eq -> (=) | Lt -> (<=) | Lte -> (<=) in
     op v1 v2
  | And(sc_list) -> List.for_all (trivial f_env n_env) sc_list
  | Let(id_e_list, sc) ->
     let n_env =
       List.fold_left
         (fun acc (id, s) -> Env.add id (eval n_env s) acc) 
         n_env id_e_list in
     trivial f_env n_env sc
  | If(sc1, sc2, sc3) ->
     if trivial f_env n_env sc1 then trivial f_env n_env sc2 
     else trivial f_env n_env sc3
  | App(f, e_list) ->
     let v_list = List.map (eval n_env) e_list in
     let v = try Env.find f f_env with Not_found -> raise Fail in
     (* (f_env f) v_list *) v v_list
  | Fix(id_id_list_sc_list, sc) ->
     (* [let rec f1 n1... = sc1 and f2 n2... = sc2 and ... in sc] *)
     let rec f_env_rec =
       lazy (List.fold_left 
               (fun f_acc (id, id_list, sc) -> 
                 Env.add id 
                   (fun v_list -> 
                     let n_env = 
                       List.fold_left2 (fun acc id v -> Env.add id v acc)
                         n_env id_list v_list in
                     trivial (Env.append (Lazy.force f_env_rec) f_env) n_env sc)
                   f_acc)
               f_env id_id_list_sc_list) in
     trivial (Env.append (Lazy.force f_env_rec) f_env) n_env sc
  
(* free variables *)
let rec fv bounded acc si =
  match si with
  | Sint _ -> acc
  | Svar(n) -> if S.mem n bounded || S.mem n acc then acc else S.add n acc
  | Sfrac { num } -> fv bounded acc num
  | Sop(_, si1, si2) -> fv bounded (fv bounded acc si1) si2

let rec fv_constraints bounded acc sc =
  match sc with
  | True | False -> acc
  | And(sc_list) -> List.fold_left (fv_constraints bounded) acc sc_list
  | Rel { lhs; rhs } -> fv bounded (fv bounded acc lhs) rhs
  | Let(id_e_list, sc) ->
     let acc =
       List.fold_left (fun acc (_, s) -> fv bounded acc s) acc id_e_list in
     let bounded =
       List.fold_left (fun acc (id, _) -> S.add id bounded) bounded id_e_list in
     fv_constraints bounded acc sc
  | If(sc1, sc2, sc3) ->
     fv_constraints bounded
       (fv_constraints bounded (fv_constraints bounded acc sc1) sc2) sc3 
  | App(n, e_list) ->
     let acc = if S.mem n bounded || S.mem n acc then acc else S.add n acc in
     List.fold_left (fv bounded) acc e_list
  | Fix(id_id_list_sc_list, sc) ->
     let bounded =
       List.fold_left
         (fun acc (id, _, _) -> S.add id acc) bounded id_id_list_sc_list in
     let acc =
       List.fold_left 
         (fun acc (_, id_list, sc) ->
           let bounded =
             List.fold_left (fun acc id -> S.add id acc) bounded id_list in
           fv_constraints bounded acc sc)
         acc id_id_list_sc_list in
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
  | Sop(op, si1, si2) -> apply op (subst env si1) (subst env si2)
  | Sfrac { num; denom } -> frac (subst env num) denom
  | Svar(n) ->
     try Env.find n env with | Not_found -> raise Fail

let subst_in_constraints env sc =
  if Env.is_empty env then sc
  else
    let id_e_list = Env.fold (fun id e acc -> (id, e) :: acc) env [] in
    Let(id_e_list, sc)

(* matching. Given [si] and [pat] generate a boolean condition *)
(* when [pat] matches [si]; produce definitions [xi = ei] if necessary *)
let rec matches { Zelus.pat_desc } si =
  match pat_desc with
  | Ewildpat -> [], True
  | Econstpat(Eint(i)) -> [], Rel { rel = Eq; lhs = si; rhs = Sint(i) }
  | Evarpat(x) -> [(x, si)], True
  | Etypeconstraintpat(pat, _) -> matches pat si
  | Ealiaspat(pat, x) ->
     let def_list, sc = matches pat si in
     (x, si) :: def_list, sc
  | _ -> raise Fail

(* define a conditional constraint [if cond1 then c1 else ... else cn] *)
let rec if_list def_cond_sc_list =
  let let_in l sc = match l with | [] -> sc | _ -> Let(l, sc) in
  let conditional sc sc_true sc_false =
    match sc with | True -> sc_true | _ -> If(sc, sc_true, sc_false) in
  match def_cond_sc_list with
  | [] -> True
  | [(def_list,_ ), sc] -> let_in def_list sc 
  | ((def_list, cond), sc) :: def_cond_sc_list ->
     conditional cond (let_in def_list sc) (if_list def_cond_sc_list)

(* An alternative representation. *)
(* Suppose that variables are ordered x0 < ... < xn *)
(* represent the polynomial as a value of the inductive type *)
(* pi = xi.pk + pj where j => k /\ i > k, with Pk a polynomial. It is the *)
(* result of the Euclidian division of pi by variable xi. *)

