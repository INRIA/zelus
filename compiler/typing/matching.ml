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

(* A generic pattern-matching verifier based on Luc Maranget's paper at JFLA *)
(* Author: Adrien Guatto 2009                                             *)
(* See http://pauillac.inria.fr/~maranget/papers/warn/index.html          *)
(* Implemented originally in the Lucid Synchrone compiler, V4 by A.Guatto *)

(** Useful functions *)
let rec repeat n a = match n with | 0 -> [] | n -> a :: (repeat (n - 1) a)
                                                        
(* keep l n returns the rest l' such that l = p @ l' with p of size n *)
let rec keep l n = match (l, n) with
  | (_, 0) -> invalid_arg "keep"
  | (h :: _, 1) -> h
  | (_ :: t, n) -> keep t (n - 1)
  | _ -> invalid_arg "keep"

(* keep l n returns the prefix p of size n such that l = p @ l' *)
let rec drop l n = match (l, n) with
  | (_, 0) -> invalid_arg "drop"
  | (_ :: t, 1) -> t
  | (h :: t, n) -> h :: (drop t (n - 1))
  | _ -> invalid_arg "drop"

let rec range n m = if n > m then [] else n :: (range (n + 1) m)

(* split l into p and l' such that l = p @ l with p of size n *)
let separate n l =
  let rec f acc n l = match (n, l) with
    | (0, _) -> (acc, l)
    | (n, h :: t) -> f (h :: acc) (n - 1) t
    | _ -> assert false in
  if n > List.length l
  then invalid_arg "separate"
  else
    let (p, l) = f [] n l in
    (List.rev p, l)

(* Syntax for patterns, and pretty-printers                         *)

(** Generic pattern, basically constructors with holes and alternation,
    tagged with any type. *)
type 'a pattern =
  | Pany
  | Por of 'a pattern * 'a pattern
  | Pconstr of 'a * 'a pattern list
and 'a patt_vec = 'a pattern list
(* Row vectors *)
and 'a patt_matrix = 'a patt_vec list

(* Module type for constructor signatures                           *)

(** Module type for pattern signatures. *)
module type SIG =
sig
  type tag
  val compare : tag -> tag -> int
  val arity : tag -> int
  val is_complete : tag list -> bool
  val not_in : tag list -> tag

  type pattern_ast
  val inject : pattern_ast -> tag pattern
  val eject : tag pattern -> pattern_ast
end

(* The algorithm itself, parametrized over signatures               *)

module PATTERN_CHECKER = functor (S : SIG) ->
struct
  module SSet =
    Set.Make(struct
      type t = S.tag
      let compare = S.compare
    end)
  (* Used for signature management. *)
  let uniq l = SSet.elements (List.fold_right SSet.add l SSet.empty)

  (* Wrappers for S's signature functions. Well, we should switch to something
     more efficient than sorting at each call. *)
  let is_complete sigma = S.is_complete (uniq sigma)
  let not_in sigma = S.not_in (uniq sigma)

  (** Extract constructors from pattern. *)
  let rec head_constrs h = match h with
    | Pconstr (c, q) -> [(c, List.length q)]
    | Por (l, r) -> head_constrs l @ head_constrs r
    | Pany -> []

  (** Implementation of S(c,p) as described in the paper's first part. *)
  let rec matS c ar p =
    let vecS pv = match pv with
      | [] -> assert false
      | Pconstr (c', r') :: pv' -> if S.compare c c' = 0 then [r' @ pv'] else []
      | Pany :: pv' -> [repeat ar Pany @ pv']
      | Por (t1, t2) :: pv' -> matS c ar [t1 :: pv'; t2 :: pv'] in
    List.concat (List.map vecS p)

  (** Implementation of D(p) as described in the paper's first part. *)
  let rec matD p =
    let vecD pv = match pv with
      | Pconstr _ :: _ -> []
      | Pany :: pv' -> [pv']
      | Por (t1, t2) :: pv' -> matD [t1 :: pv'; t2 :: pv']
      | _ -> assert false in
    List.concat (List.map vecD p)

  (** U(p,q) from the paper. Most important function, called by higher level
      ones. Tests the usefulness of q relatively to p. *)
  let rec algU p q =
    match (p, q) with
      | ([], _) -> true       (* p has no lines *)
      | (_ :: _, []) -> false (* p has no columns *)

      | (h :: t,  Pconstr (c, r) :: q') ->
          let p' = matS c (List.length r) p in
          algU p' (r @ q')

      | (h :: t, Por (r1, r2) :: q') ->
          algU p (r1 :: q') || algU p (r2 :: q')

      | (h :: t, Pany :: q') ->
          let sigma =
            List.concat (List.map (fun v -> head_constrs (List.hd v)) p) in
          let algU_constr (c_k, ar_k) =
            let p' = matS c_k ar_k p in
            algU p' (repeat ar_k Pany @ q') in
          let sigma_used = List.exists algU_constr sigma in
          sigma_used || (if not (is_complete (List.map fst sigma))
                         then algU (matD p) q' else false)


    (** Type used for efficient testing of usefulness and redundancy of
        pattern-matching cases. *)
    type 'a trivec = { p : 'a patt_vec;
                       q : 'a patt_vec;
                       r : 'a patt_vec }
    and 'a trimat = 'a trivec list


    (** Second de finition of S(c,p) for tri-matrices. *)
    let rec trimatS c arity mv =
      let filter_line l = match l.p with
          | Pconstr (c', t) :: p' ->
              if S.compare c c' = 0 then [{ l with p = t @ p' }] else []
          | Pany :: p' ->
              [{ l with p = repeat arity Pany @ p' }]
          | Por (t1, t2) :: p' ->
              trimatS c arity [{ l with p = t1 :: p' }; { l with p = t2 :: p' }]
          | _ -> assert false in
      List.concat (List.map filter_line mv)

    (** {i shift1 l} shifts an element from {i l.p} to {i l.q}. *)
    let shift1 l = match l.p with
      | p :: p' -> { l with p = p'; q = p :: l.q }
      | _ -> assert false

    (** {i shift2 l} shifts an element from {i l.p} to {i l.r}. *)
    let shift2 l = match l.p with
      | p :: p' -> { l with p = p'; r = p :: l.r }
      | _ -> assert false

    (** {i S.tag pattern list option} is used for results of usefulness testing
        for Or(r1,r2) patterns. Some [] means that r1 and r2 are both useful,
        Some [r1] (resp. Some [r2]) means that r1 (resp. r2) is useless, and 
        None means that both are. *)

    (** The following functions implement useful shortcuts. *)

    let simple_union e e' = match (e, e') with
      | (Some l, Some l') -> Some (l @ l')
      | (None, _) | (_, None) -> None

    let union r1 r2 e' e'' = match (e', e'') with
      | (Some [], Some []) -> Some []
      | (None, None) -> None
      | (Some [], None) -> Some [r2]
      | (None, Some []) -> Some [r1]

      | (Some [], Some (_ :: _)) -> e''
      | (Some (_ :: _), Some []) -> e'

      | (None, Some ((_ :: _) as t)) -> Some (r1 :: t)
      | (Some ((_ :: _) as t), None) -> Some (r2 :: t)

      | (Some ((_ :: _) as t'), Some ((_ :: _) as t'')) -> Some (t' @ t'')

    (** Efficient usefulness check with special Or pattern management. *)
    let rec algU' m v =
      match v.p with
          (* Phase one *)
        | Pconstr (c, t) :: p' ->
            algU' (trimatS c (List.length t) m) { v with p = t @ p' }
        | Pany :: _ ->
            algU' (List.map shift1 m) (shift1 v)
        | Por _ :: _ ->
            algU' (List.map shift2 m) (shift2 v)
        | [] ->
            (* Phase two *)
            begin match v.r with
              | [] ->
                  let qm = List.map (fun l -> l.q) m in
                  if algU qm v.q then Some [] else None
              | _ :: _ ->
                  let rec compute_Ej j =
                    begin match List.nth v.r (j - 1) with
                      | Por (t1, t2) ->
                          let f l =
                            let r_j = keep l.r j
                            and r_woj = drop l.r j in
                            { p = [r_j]; q = r_woj @ l.q; r = [] } in
                          let rv_woj = drop v.r j in
                          let m' = List.map f m in
                          let m'' =
                            m' @ [{ p = [t1]; q = drop v.r j @ v.q; r = [] }] in
                          let r1 = algU' m'
                            { p = [t1]; q = rv_woj @ v.q; r = [] }
                          and r2 = algU' m''
                            { p = [t2]; q = rv_woj @ v.q; r = [] } in
                          union t1 t2 r1 r2
                      | _ -> assert false
                    end in
                  let j_list = range 1 (List.length (List.hd m).r) in
                  let computed_Ej = List.map compute_Ej j_list in
                  List.fold_left simple_union (Some []) computed_Ej
            end

    (** Completely construct a non-matched pattern. If none is returned,
        this matrix is exhaustive. *)
    let rec algI m n = match (m, n) with
      | ([], 0) -> Some []
      | ([] :: _, 0) -> None
      | (m, n) ->
          let sigma =
            List.concat (List.map (fun v -> head_constrs (List.hd v)) m) in
          let sigma_c = List.map fst sigma in
          let default =
            if is_complete sigma_c
            then None
            else algI (matD m) (n - 1) in
          begin match default with
            | Some p ->
                begin match sigma with
                  | [] -> Some (Pany :: p)
                  | _ :: _ ->
                      let c' = not_in sigma_c in
                      Some (Pconstr (c', repeat (S.arity c') Pany) :: p)
                end
            | None ->
                let rec traverse_sigma sigma = match sigma with
                  | [] -> None
                  | (c, ar) :: sigma' ->
                      let res =
                        algI (matS c ar m) (ar + n - 1) in
                      begin match res with
                        | None -> traverse_sigma sigma'
                        | Some v ->
                            let (r, p) = separate ar v in
                            Some (Pconstr (c, r) :: p)
                      end in
                traverse_sigma sigma
          end

    type result = { not_matched : S.pattern_ast option;
                    redundant_patterns : S.pattern_ast list; }

    let check m =
      let m' = List.map (fun v -> [S.inject v]) m in
      match m' with
        | [] -> invalid_arg "check"
        | v :: _ ->
            { not_matched =
                begin
                  let n = List.length v in
                  match algI m' n with
                    | None -> None
                    | Some [p] -> Some (S.eject p)
                    | _ -> assert false
                end;
              redundant_patterns =
                begin
                  let make_trivec v = { p = v; q = []; r = [] } in
                  let make_trimat m = List.map make_trivec m in
                  let check_line (m, red) v =
                    let r = algU' (make_trimat m) (make_trivec v) in
                    (m @ [v], match r with
                       | Some [] -> red
                       | Some r -> List.map S.eject r @ red
                       | None -> List.map S.eject v @ red) in
                  let (_, red) = List.fold_left
                    check_line ([(List.hd m')], []) (List.tl m') in
                  red;
                end }
  end
