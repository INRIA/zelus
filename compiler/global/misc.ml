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

(* useful stuff *)

(* version of the compiler *)
let version = "Zélus"
let subversion = VERSION
let date = DATE

let header_in_file =
  "The " ^ version ^ " compiler, version " ^ subversion ^ "\n\  (" ^ date ^ ")"

(* generic data-structres for sets and symbol tables *)
module S = Set.Make (struct type t = string let compare = compare end)
module Env = Map.Make (struct type t = string let compare = compare end)


(* standard module *)
let name_of_stdlib_module = "Stdlib"

let standard_lib = try Sys.getenv "ZLLIB" with Not_found -> STDLIB

(* list of modules initially opened *)
let default_used_modules = ref [name_of_stdlib_module]

(* load paths *)
let load_path = ref ([standard_lib])

let set_stdlib p =
  load_path := [p]
and add_include d =
  load_path := d :: !load_path;;

(* where is the standard library *)
let locate_stdlib () =
  Printf.printf "%s\n" standard_lib

let show_version () =
  Printf.printf "The %s compiler, version %s (%s)\n"
    version subversion date;
  Printf.printf "Std lib: "; locate_stdlib ()

(* sets the main simulation node *)
let simulation_node = ref None
let set_simulation_node (n:string) = simulation_node := Some(n)

(* sets the output filepath *)
let outname = ref None
let set_outname (n:string) = outname := Some(n)

(* sets the checking flag *)
let number_of_checks = ref 0
let set_check (n: int) = number_of_checks := n

(* sampling the main loop on a real timer *)
let sampling_period = ref 0.0
let set_sampling_period p = sampling_period := p

(* level of inlining *)
let inlining_level = ref 10
let set_inlining_level l = inlining_level := l
let inline_all = ref false

(* turn on the discrete zero-crossing detection *)
let dzero = ref false

(* other options of the compiler *)
let verbose = ref false
let vverbose = ref false
let print_types = ref false
let print_causality_types = ref false
let print_initialization_types = ref false
let typeonly = ref false
let use_gtk = ref false
let no_causality = ref false
let no_initialisation = ref false
let no_opt = ref false
let no_deadcode = ref false
let no_simplify_causality_type = ref false
let no_reduce = ref false
let no_warning = ref false
let zsign = ref false
let with_copy = ref false
let use_rif = ref false

let lmm_nodes = ref S.empty
let set_lmm_nodes (n: string) =
  lmm_nodes := S.add n !lmm_nodes

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

(* generic and non generic variables in the various type systems *)
let generic = -1
let notgeneric = 0
let maxlevel = max_int

let binding_level = ref 0
let top_binding_level () = !binding_level = 0

let push_binding_level () = binding_level := !binding_level + 1
let pop_binding_level () =
  binding_level := !binding_level - 1;
  assert (!binding_level > generic)
let reset_binding_level () = binding_level := 0

(* general iterators and functions *)
let optional f acc = function
  | None -> acc
  | Some x -> f acc x

let optional_unit f acc = function
  | None -> ()
  | Some x -> f acc x

let optional_map f = function
  | None -> None
  | Some(x) -> Some(f x)

let optional_with_map f acc = function
  | None -> None, acc
  | Some(x) -> let x, acc = f acc x in Some(x), acc

let optional_get = function
  | Some x -> x
  | None   -> assert false

let rec iter f = function
  | [] -> []
  | x :: l -> let y = f x in y :: iter f l

let fold f l = List.rev (List.fold_left f [] l)

let from i =
  let rec fromrec acc i =
    match i with
    | 0 -> acc
    | _ -> fromrec ( i :: acc) (i - 1) in
  fromrec [] i

let map_fold f acc l =
  let rec maprec acc = function
    | [] -> [], acc
    | x :: l ->
       let y, acc = f acc x in
       let l, acc = maprec acc l in
       y :: l, acc in
  maprec acc l

(* takes the first patterns of the list, except the last one *)
let rec firsts = function
    | [] -> assert false
    | [p] -> [], p
    | p :: l -> let head, tail = firsts l in p :: head, tail

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

(* error during the whole process *)
exception Error

(* Internal error in the compiler. *)
let internal_error message printer input =
  Format.eprintf "@[Internal error (%s)@. %a@.@]" message printer input;
  raise Error
