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

(** The data-structure to represent a state *)
module State =
  struct
    type 'a t = (* ' *)
        | Empty
        | Cons of 'a * 'a t
        | Par of 'a t * 'a t
	| Seq of 'a t * 'a t
    let singleton x = Cons(x, Empty)
    let cons x s = Cons(x, s)
    let seq s1 s2 =
      match s1, s2 with
        | (Empty, s) | (s, Empty) -> s
        | _ -> Seq(s1, s2)
    let par s1 s2 =
      match s1, s2 with
        | (Empty, s) | (s, Empty) -> s
        | _ -> Par(s1, s2)
    let empty = Empty
    let is_empty s = (s = empty)
    let rec fold f s acc = match s with
      | Empty -> acc
      | Cons(x, l) -> f x (fold f l acc)
      | Par(l1, l2) -> fold f l1 (fold f l2 acc)
      | Seq(l1, l2) -> fold f l1 (fold f l2 acc)
    let list acc s = fold (fun l ls -> l :: ls) s acc

    let cons_list xs s = List.fold_left (fun s x -> Cons (x, s)) s (List.rev xs)

    let rec map f s = match s with
      | Empty -> Empty
      | Cons(x, l) -> Cons(f x, map f l)
      | Par(l1, l2) -> Par(map f l1, map f l2)
      | Seq(l1, l2) -> Seq(map f l1, map f l2)

    let rec iter f s = match s with
      | Empty -> ()
      | Cons(x, l) -> (f x; iter f l)
      | Par(l1, l2) | Seq(l1, l2) -> (iter f l1; iter f l2)

    let rec partition f s =
      match s with
      | Empty -> Empty, Empty
      | Cons(x, l) ->
         let left, right = partition f l in
         if f x then Cons(x, left), right else left, Cons(x, right)
      | Par(l1, l2) ->
         let left1, right1 = partition f l1 in
         let left2, right2 = partition f l2 in
         Par(left1, left2), Par(right1, right2)
      | Seq(l1, l2) ->
         let left1, right1 = partition f l1 in
         let left2, right2 = partition f l2 in
         Seq(left1, left2), Seq(right1, right2)

    let fprint_t fprint_v ff s =
      let rec print ff s =
	match s with
	| Empty -> Format.fprintf ff "{}"
	| Cons(x, s) ->
	   Format.fprintf ff "@[Cons(%a,@ %a)@]" fprint_v x print s
	| Par(s1, s2) ->
	   Format.fprintf ff "@[Par(%a,@ %a)@]" print s1 print s2
	| Seq(s1, s2) ->
	   Format.fprintf ff "@[Seq(%a,@ %a)@]" print s1 print s2 in
      Format.fprintf ff "@[<hov>%a@]" print s
  end
