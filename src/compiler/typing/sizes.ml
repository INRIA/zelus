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

(* decision for equality/inequalities constraints between polymial sizes *)
(* simple simplification functions *)
(* sizes are of the form:  s ::= s + s | s * s | xi | v | xi/v *)
(* constraints are: sc ::= sc & sc | if sc then sc else sc | true | false *)
(*                      | forall i < s do sc | s = s | s <= s | s < s *)
(*                      | let rec f(n1,...,nk) = c in c | f(s1,...,sn) *)
open Ident
open Defsizes

exception Maybe
(* raise an exception when the decision algorithm fails to decide *)
(* that [sc] is true or false. For example, [sc] containts a free *)
(* variable and the decision algorithm is not good enough *)
  
(* normal form for polynomial sizes : some of products *)
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
    (* to [mi] is associated the coefficient [pi] *)
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
        let const v =
          (* [v] is represented as v * one *)
          if v = 0 then zero else M.singleton Product.one v

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
        let to_size_expression m =
          let v_list = M.to_list m in
          let sum positive acc s2 =
            (* if [positive] then [acc + s2] else [acc - s2] *)
            match s2 with
            | Sint(0) -> acc
            | _ -> let op = if positive then Splus else Sminus in
                   Sop(op, acc, s2) in
          let mult p m =
            match p with
            | 0 -> assert false
            | 1 -> (* [1 * m = m] *)
               Product.explicit m
            | _ ->
               (* [p * 1 = p] *)
               if Product.is_one m then Sint(p) else
                 Sop(Smult, Sint(p), Product.explicit m) in
          List.fold_left
            (fun acc (m, p) ->
              let positive, p = if p >= 0 then true, p else false, - p in
              sum positive acc (mult p m)) (Sint(0)) v_list

        (* implicit representation *)
        let rec from_size_expression si =
          match si with
          | Sint(i) -> const i
          | Svar(x) -> var x
          | Sop(op, si1, si2) ->
             let e1 = from_size_expression si1 in
             let e2 = from_size_expression si2 in
             let op = 
               match op with Splus -> sum | Sminus -> minus | Smult -> mult in
             op e1 e2
          | Sfrac _ ->
             (* the term must have been normalized before *)
             assert false
      end
  end

(* To be done: an alternative representation for multi-variate polynomials *)
(* Suppose that variables are ordered x0 < ... < xn *)
(* represent the polynomial as a value of the inductive type *)
(* pi = xi.pk + pj where j => k /\ i > k, with Pk a polynomial. It is the *)
(* result of the Euclidian division of pi by variable xi. *)

(* main entries *)
let const v = Sint v
let zero = const 0
let one = const 1
let var x = Svar(x)
let plus si1 si2 = Sop(Splus, si1, si2)
let minus si1 si2 = Sop(Sminus, si1, si2)
let uminus si = Sop(Sminus, zero, si)
let mult si1 si2 = Sop(Smult, si1, si2)

(* elimination of div operations in size expressions *)
let normalize si =
  let module Table =
    Map.Make
      (struct type t = Defsizes.exp * int let compare = Stdlib.compare end) in
  let rec norm table si =
    match si with
    | Sint _ | Svar _ -> si, table
    | Sop(op, si1, si2) ->
       let si1, table = norm table si1 in
       let si2, table = norm table si2 in
       Sop(op, si1, si2), table
    | Sfrac { num; denom } ->
       let e, table = norm table num in
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
  let si, table = norm Table.empty si in
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

(* build size expressions *)
let apply op si1 si2 =
  match si1, si2 with
  | Sint(v1), Sint(v2) ->
     let op = match op with | Splus -> (+) | Sminus -> (-) | Smult -> ( * ) in
     Sint(op v1 v2)
  | _ -> Sop(op, si1, si2)

let frac num denom =
  match num with | Sint(vi) -> Sint(vi / denom) | _ -> Sfrac { num; denom }

(* substitution in a size expression *)
let rec subst_in_size env si =
  match si with
  | Sint _ -> si
  | Sop(op, si1, si2) ->
     apply op (subst_in_size env si1) (subst_in_size env si2)
  | Sfrac { num; denom } -> frac (subst_in_size env num) denom
  | Svar(n) ->
     try Env.find n env with | Not_found -> si

(* substitution in a constraint. Assume that there is no name conflict *)
(* that is, free variables in [env] do not appear in [sc] *)
let rec subst_in_constraint env sc =
  match sc with
  | True | False -> sc
  | And(sc_list) -> And(List.map (subst_in_constraint env) sc_list)
  | Rel { rel; lhs; rhs } -> 
     Rel { rel; lhs = subst_in_size env lhs; rhs = subst_in_size env rhs }
  | If(sc1, sc2, sc3) ->
     If(subst_in_constraint env sc1,
        subst_in_constraint env sc2, subst_in_constraint env sc3)
  | App(n, e_list) ->
     App(n, List.map (subst_in_size env) e_list)
  | Let(id_e_list, sc) ->
     Let(List.map (fun (id, e) -> (id, subst_in_size env e)) id_e_list,
         subst_in_constraint env sc)
  | Fix(id_id_list_sc_list, sc) ->
     Fix(List.map 
           (fun (id, id_list, sc) -> (id, id_list, subst_in_constraint env sc)) 
           id_id_list_sc_list,
         subst_in_constraint env sc)
  | Forall(id, e, sc) ->
     Forall(id, subst_in_size env e, subst_in_constraint env sc)
  | Loc(loc, sc) -> Loc(loc, subst_in_constraint env sc)

(* for the moment, we do not use equations generated during the normalization *)
let normalize si =
  let si, _ = normalize si in
  SumOfProducts.SumProduct.from_size_expression si

(* given a size expression [si], try to decompose it into [n = si'] *)
(* such that [n - si' = 0 where [n] is a meta size-variable that appear in [env] *)
(* [raise Fail_to_decompose] is it fails *)
exception Fail_to_decompose

let decompose meta_size_variables si =
  (* [positive = true] iff [si = n + si'] and [si = n - si'] otherwise *)
  let rec decompose_rec si =
    match si with
    | Svar(n) when Env.mem n meta_size_variables -> n, true, Sint(0)
    | Sop(Splus, Svar(n), si') when Env.mem n meta_size_variables -> n, true, si'
    | Sop(Splus, si', Svar(n)) when Env.mem n meta_size_variables -> n, true, si'
    | Sop(Sminus, Svar(n), si') when Env.mem n meta_size_variables -> n, false, si'
    | Sop(Sminus, si', Svar(n)) when Env.mem n meta_size_variables -> n, false, si'
    | Sop(Splus, si1, si2) ->
       begin try
           (* if [si1 = n + si11] then [si = n + (si11 + si2)] *)
           (* if [si1 = n - si11] then [si = n + (si2 - si11)] *)
           let n, positive, si11 = decompose_rec si1 in
           n, true,
           if positive then Sop(Splus, si11, si2) else Sop(Sminus, si2, si11)
         with
         | Fail_to_decompose ->
            (* if [si2 = (n + si22) then [si = n + (si1 + si22)] *)
            (* if [si2 = (n - si22) then [si = n + (si1 - si22)] *)
            let n, positive, si22 = decompose_rec si2 in
            n, true, Sop((if positive then Splus else Sminus), si1, si22)
       end
    | Sop(Sminus, si1, si2) ->
       begin try
           (* if [si1 = n + si11] then [si = n + (si11 - si2)] *)
           (* if [si1 = n - si11] then [si = n - (si11 + si2)] *)
           let n, positive, si11 = decompose_rec si1 in
           n, positive,
           if positive then Sop(Sminus, si11, si2) else Sop(Splus, si11, si2)
         with
         | Fail_to_decompose ->
            (* [si1 - (n + si22) = 0] iff [n + (si22 - si1)] = 0 *)
            (* [si1 - (n - si22) = 0] iff [n + (si1 - si22) = 0 *)
            (* that is: if [si2 = (n + si22) then [si = n + (si22 - si1)] *)
            (* that is: if [si2 = (n - si22) then [si = n + (si1 - si22)] *)
            let n, positive, si22 = decompose_rec si2 in
            n, true,
            if positive then Sop(Sminus, si22, si1) else Sop(Sminus, si1, si22)
       end
    | _ -> raise Fail_to_decompose in
  let n, positive, si = decompose_rec si in
  n, if positive then uminus si else si

(* Decision algorithm for equality for two size expression [si1] and [si2]. *)
(* It is a very basic decision algorithm since inequality constraints *)
(* are not taken into account and equalities are only taken into account *)
(* when they are of the form [n = si] *)
(* This is not a problem for correctness and completeness since *)
(* size constraints that are not trivially true or false *)
(* will be ultimately evaluated when size variables are known. *)
(* Yet, we shall complement this stategy with a more advanced decision *)
(* algorithms to detect errors early and improve diagnosis *)
let simple_equal si1 si2 =
  let open SumOfProducts in
  let sp = normalize (minus si1 si2) in
  if SumProduct.is_surely_zero sp then true
  else if SumProduct.is_surely_not_zero sp then false
  else (* add it to the constraint environment *)
    try
      let si = SumProduct.to_size_expression sp in
      (* the environment is used to know which size variable *)
      (* is a meta variable *)
      let meta_size_variables = Defsizes.get_unconstrained_size_variables () in
      let n, si = decompose meta_size_variables si in
      Defsizes.intro_substitution_for_size_variables n si;
      true
    with
    | Fail_to_decompose ->
       Defsizes.add (Rel { rel = Eq; lhs = si1; rhs = si2 }); true

let equal si1 si2 =
  (* apply substitutions for meta size-variables *)
  let env = Defsizes.get_substitution_for_size_variables () in
  let si1 = subst_in_size env si1 in
  let si2 = subst_in_size env si2 in
  simple_equal si1 si2

let surely_equal si1 si2 =
  let open SumOfProducts in
  (* apply substitutions for meta size-variables *)
  let env = Defsizes.get_substitution_for_size_variables () in
  let si11 = subst_in_size env si1 in
  let si22 = subst_in_size env si2 in
  let sp = normalize (minus si11 si22) in
  SumProduct.is_surely_zero sp

(* is a pattern [p_i] in a [match size si with | (p_i -> e_i)_i] *)
(* equal to a size [si] *)
let rec pattern_equal { Zelus.pat_desc } si =
  match pat_desc, si with
  (* the cases where it returns [true] *)
  | Ewildpat, _ -> true
  | Econstpat(Eint(i)), Sint(j) when i = j -> true
  | Evarpat(x), Svar(y) when Ident.compare x y = 0 -> true
  | Ealiaspat(p, x), Svar(y) when Ident.compare x y = 0 -> true
  | Etypeconstraintpat(p, _), _ -> pattern_equal p si
  | Eorpat(p1, p2), _ ->
     (pattern_equal p1 si) && (pattern_equal p2 si)
  | Ealiaspat(p, _), _ -> pattern_equal p si
  | _ -> false

let compare loc cmp si1 si2 =
  let exception Maybe in
  let open SumOfProducts in
  try
    let env = Defsizes.get_substitution_for_size_variables () in
    let si1 = subst_in_size env si1 in
    let si2 = subst_in_size env si2 in
    let result = match cmp with
      | Eq ->
         (* equality of two sizes is treated specially *)
         simple_equal si1 si2
      | (* si1 < si2, that is, si1 + 1 <= si2, that is, si2 - (si1 + 1) *)
        Lt ->
         let sp = normalize (minus si2 (plus si1 one)) in
         if SumProduct.is_surely_positive sp then true
         else if SumProduct.is_surely_not_positive sp then false
         else raise Maybe
      | Lte ->
         let sp = normalize (minus si2 si1) in
         if SumProduct.is_surely_positive sp then true
         else if SumProduct.is_surely_not_positive sp then false
         else raise Maybe in
    result
  with
  | Maybe ->
     (* add it to the constraint environment *)
     Defsizes.add (Loc(Location.current_iname loc,
                       Rel { rel = cmp; lhs = si1; rhs = si2 })); true

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

(* evaluation of sizes. Raises Maybe if it contains un unbound variable *)
let rec eval n_env si =
  match si with
  | Sint(i) -> i
  | Sfrac { num; denom} ->
      let v = eval n_env num in
      v / denom
  | Svar(x) ->
      let v =
        try Env.find x n_env with Not_found -> raise Maybe in v
  | Sop(op, si1, si2) ->
     let v1 = eval n_env si1 in
     let v2 = eval n_env si2 in
     let op = match op with | Splus -> (+) | Smult -> ( * ) | Sminus -> (-) in
     op v1 v2

(* fix-point computation of an environment of functions *)
(* [let rec f1 n1... = sc1 and f2 n2... = sc2 and ... in sc] *)
let letrec eval_constraint f_env n_env id_id_list_sc_list =
  let rec f_env_fix =
    lazy (List.fold_left 
            (fun f_acc (id, id_list, sc) -> 
              Env.add id 
                (fun v_list -> 
                  let n_env = 
                    List.fold_left2 (fun acc id v -> Env.add id v acc)
                      n_env id_list v_list in
                  eval_constraint (Lazy.force f_env_final) n_env sc)
                 f_acc)
            Env.empty id_id_list_sc_list)
  and f_env_final = lazy (Env.append (Lazy.force f_env_fix) f_env) in
  Lazy.force f_env_final

(* evaluation of constraints. *)
(* [f_env]: environment of functions; [n_env]: environment of sizes *)
let rec eval_constraint f_env n_env sc =
  match sc with
  | True -> true
  | False -> false
  | Rel { rel; lhs; rhs } ->
     let v1 = eval n_env lhs in
     let v2 = eval n_env rhs in
     let op = match rel with | Eq -> (=) | Lt -> (<) | Lte -> (<=) in
     op v1 v2
  | And(sc_list) -> List.for_all (eval_constraint f_env n_env) sc_list
  | Let(id_e_list, sc) ->
     let n_env =
       List.fold_left
         (fun acc (id, s) -> Env.add id (eval n_env s) acc) 
         n_env id_e_list in
     eval_constraint f_env n_env sc
  | If(sc1, sc2, sc3) ->
     if eval_constraint f_env n_env sc1 then eval_constraint f_env n_env sc2 
     else eval_constraint f_env n_env sc3
  | App(f, e_list) ->
     let v_list = List.map (eval n_env) e_list in
     let v = try Env.find f f_env with Not_found -> raise Maybe in
     v v_list
  | Fix(id_id_list_sc_list, sc) ->
     let f_env_final = letrec eval_constraint f_env n_env id_id_list_sc_list in
     eval_constraint f_env_final n_env sc
  | Forall(id, e, sc) ->
     let rec for_all v f =
       if v <= 0 then true else (f v) && (for_all (v-1) f) in
     let v = eval n_env e in
     for_all (v-1) (fun v -> eval_constraint f_env (Env.add id v n_env) sc)
  | Loc(_, sc) -> eval_constraint f_env n_env sc


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
       List.fold_left (fun acc (id, _) -> S.add id acc) bounded id_e_list in
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
  | Forall(id, e, sc) ->
     let acc = fv_constraints (S.add id bounded) acc sc in
     fv bounded acc e
  | Loc(_, sc) -> fv_constraints bounded acc sc

(* Localisation of errors when a constraints is not satisfied *)
(* The check function and the localisation function could be merged *)
(* into one for better efficiency *)
let localise f_env n_env sc =
  (* simplify an environment; keep only variables that are free in a size *)
  (* constraint *)
  let clear n_env sc =
    let acc = fv_constraints S.empty S.empty sc in
    Env.filter (fun x _ -> S.mem x acc) n_env in
  let exception Error of 
        { f_loc_list: Location.ft list; (* [floc1;...;flocn] *)
          (* list of file/location in the source *)
          (* to get constraint [sc] which is unsatisfied *)
          (* in environment [env] *)
          (* [floc1] is the closest *)
          nested_env: int Env.t; (* environment for size variables *)
          nested_sc: exp constraints
          (* the size expression that is not satisfied *)
        } in
  let rec localise f_loc_list f_env n_env sc =
    match sc with
    | True | False | Rel _ | App _ ->
       let v = eval_constraint f_env n_env sc in
       let n_env = clear n_env sc in
       if v then true
       else raise (Error { f_loc_list; nested_env = n_env; nested_sc = sc })
    | And(sc_list) ->
       List.for_all (localise f_loc_list f_env n_env) sc_list
    | Let(id_e_list, sc) ->
       let n_env =
         List.fold_left
           (fun acc (id, s) -> Env.add id (eval n_env s) acc) 
           n_env id_e_list in
       localise f_loc_list f_env n_env sc
    | If(sc1, sc2, sc3) ->
       if eval_constraint f_env n_env sc1 then
         localise f_loc_list f_env n_env sc2 
       else localise f_loc_list f_env n_env sc3
    | Fix(id_id_list_sc_list, sc) ->
       let f_env_final =
         letrec (localise f_loc_list) f_env n_env id_id_list_sc_list in
       localise f_loc_list f_env_final n_env sc
    | Forall(id, e, sc) ->
       let rec for_all v f =
         if v <= 0 then true else (f v) && (for_all (v-1) f) in
       let v = eval n_env e in
       for_all (v-1)
         (fun v -> localise f_loc_list f_env (Env.add id v n_env) sc)
    | Loc(f_loc, sc) -> localise (f_loc :: f_loc_list) f_env n_env sc in

  try
    let _ = localise [] f_env n_env sc in assert false
  with
    Error { f_loc_list; nested_env; nested_sc } ->
    f_loc_list, nested_env, nested_sc

let let_in env sc =
  if Env.is_empty env then sc
  else
    let id_e_list = Env.fold (fun id e acc -> (id, e) :: acc) env [] in
    Let(id_e_list, sc)

(* add a subtitution for sizes into a constraint *)

(* generate a conditional. Do a bit of by case definition to make functions *)
(* that use it simpler *)
let conditional sc sc_true sc_false =
    match sc, sc_true, sc_false with 
    | True, _, _ -> sc_true 
    | False, _, _ -> sc_false 
    | _, True, False -> sc
    | _ -> if sc_true = sc_false then sc_true else If(sc, sc_true, sc_false)

let forall id e sc =
  match sc with | True -> True | False -> False | sc -> Forall(id, e, sc)

let make_lt si1 si2 = Rel { rel = Lt; lhs = si1; rhs = si2 }
let make_eq si1 si2 = Rel { rel = Eq; lhs = si1; rhs = si2 }

(* define a conditional constraint [if cond1 then c1 else ... else cn] *)
let rec if_list def_cond_sc_list =
  let let_in l sc = match l with | [] -> sc | _ -> Let(l, sc) in
  match def_cond_sc_list with
  | [] -> True
  | [(def_list,_ ), sc] -> let_in def_list sc 
  | ((def_list, cond), sc) :: def_cond_sc_list ->
     conditional cond (let_in def_list sc) (if_list def_cond_sc_list)

(* matching. Given [si] and [pat] generate a boolean condition *)
(* when [pat] matches [si]; produce definitions [xi = ei] if necessary *)
let rec matches { Zelus.pat_desc } si =
  match pat_desc with
  | Ewildpat -> [], True
  | Econstpat(Eint(i)) -> [], Rel { rel = Eq; lhs = si; rhs = Sint(i) }
  | Evarpat(x) -> [(x, si)], True
  | Etypeconstraintpat(pat, _) -> matches pat si
  | Eorpat(p1, p2) ->
     let l1, sc1 = matches p1 si in
     let l2, sc2 = matches p2 si in
     l1 @ l2, conditional sc1 True sc2
  | Ealiaspat(pat, x) ->
     let def_list, sc = matches pat si in
     (x, si) :: def_list, sc
  | _ -> assert false

(* define the prefix order between two tuples of sizes *)
(* [(si_1,...,si_n) < (si_1',...,si_n')] iff
 *- if (si_1 < si_1') then true
 *- else if si_1 = si_1' then (si_2,...) < (si_2',...) *)
let rec decreases actual_si_list expected_si_list =
  match actual_si_list, expected_si_list with
  | [], [] -> True
  | [actual_si], [expected_si] -> make_lt actual_si expected_si
  | actual_si :: actual_si_list, expected_si :: expected_si_list ->
     conditional (make_lt actual_si expected_si) True
       (conditional 
          (make_eq actual_si expected_si) 
          (decreases actual_si_list expected_si_list) False)
  | _ -> assert false

(* given an constraint f(n1,...,n_k) and a tuple of sizes [si1,...,si_n] *)
(* applies f(si1,...,si_n) if (si1,...,si_k) < (n1,...,n_k) *)
let apply constraints actual_si_list =
  match constraints with
  | App(f, expected_si_list) ->
     conditional (decreases actual_si_list expected_si_list)
       (App(f, actual_si_list)) False
  | _ -> assert false

(* introduce a fresh size variable *)
let new_size_var loc =
  let n = Ident.fresh "_n" in
  Defsizes.intro_size_variable n loc;
  Svar(n)

