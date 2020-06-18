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

open Zelus
open Global
open Lident
open Matching
open Printf
open Location
open Deftypes
open Misc

module LANG =
  struct
    (* Never use the pattern's description on more than one-level! *)
    type tag =
      | Ttuple of int (* arity *)
      | Tconst of immediate
          (* name * arity * all variants (name/arity) *)
      | Tconstr of string * int * (string * int) list
          (* fields *)
      | Trecord of string list

    let compare = Stdlib.compare

    let pdescs = List.map (fun p -> p.p_desc)

    let arity t = match t with
      | Ttuple i -> i
      | Tconst _ -> 0
      | Tconstr (_, i, _) -> i
      | Trecord l -> List.length l

    let extract_tags l : string list =
      List.map (function
                  | Tconstr (id, _, _) -> id
                  | _ -> assert false) l

    let is_complete tl = match tl with
      | [Ttuple _] -> true
      | [Trecord _] -> true
      | [Tconst (Ebool false); Tconst (Ebool true)] -> true
      | [Tconst Evoid] -> true
      (* Well... those cannot realistically be complete. *)
      | Tconst (Eint _) :: _ -> false
      | Tconst (Efloat _) :: _ -> false
      | Tconst (Estring _) :: _ -> false
      | Tconst (Echar _) :: _ -> false (* unsure about this one. TODO:ask *)
      | Tconstr (_, _, l) :: _ ->
          (List.map fst l) = extract_tags tl
      (* In all other cases... *)
      | _ -> false

    let rec fix f x = let r = f x in if r = x then r else fix f r
    
    let not_in tl =
      (* Returns e if is not in l, or next e if it is. Iterated with Misc.fix,
         eventually returns a value absent from l. *)
      let rec try_search_absent comp next l e =
        match l with
        | [] -> e
        | h :: t ->
            if comp e h = 0
            then next e
            else begin
                if comp e h < 0
                then e (* do not walk all the list! *)
                else try_search_absent comp next t e
            end in
      match tl with (* Remember: we know tl is incomplete and well-typed ! *)

        | [Tconst (Ebool b)] -> Tconst (Ebool (not b))

        | Tconst (Eint _) :: _ ->
            let next p = match p with
              | Tconst (Eint i) -> Tconst (Eint (i + 1))
              | _ -> assert false in
            fix (try_search_absent compare next tl) (Tconst (Eint 0))

        | Tconst (Efloat _) :: _ ->
            let next p = match p with
              | Tconst (Efloat f) -> Tconst (Efloat (f +. 1.))
              | _ -> assert false in
            fix (try_search_absent compare next tl) (Tconst (Efloat 0.))

        | Tconst (Estring _) :: _ ->
            let next p = match p with
              | Tconst (Estring s) -> Tconst (Estring (s ^ "*"))
              | _ -> assert false in
            fix (try_search_absent compare next tl) (Tconst (Estring ""))

        | Tconst (Echar c) :: _ ->
            let next p = match p with
              | Tconst (Echar c) ->
                  Tconst (Echar (Char.chr (Char.code c + 1)))
              | _ -> assert false in
            fix (try_search_absent compare next tl) (Tconst (Echar 'a'))

        | Tconstr (_, _, l) :: _ ->
            let next l = List.tl l
            and cmp l x = Stdlib.compare (fst (List.hd l)) x
            and heads = extract_tags tl in
            let (name, ar) =
              List.hd (fix (try_search_absent cmp next heads) l) in
            Tconstr (name, ar, l)

        | _ -> assert false


    type pattern_ast = Zelus.pattern

    (* Translation to tagged patterns is pretty easy, we just have to look for
       each possible constructors for constructed patterns, and sort fields for
       record patterns. *)
    let rec inject p =
      let rec find_variant_type_idents s =
        match (Modules.find_type s).info.type_desc with
          | Variant_type cdi ->
              let extract_name_and_arity cd =
                (cd.qualid.id, List.length cd.info.constr_arg) in
              List.sort Stdlib.compare (List.map extract_name_and_arity cdi)
          | _ -> assert false
      and find_record_type_fields typ =
        let { t_desc = desc } = Types.typ_repr typ in
        match desc with
          | Deftypes.Tconstr (s, _, _) ->
              begin match (Modules.find_type (Modname s)).info.type_desc with
                | Record_type cdi ->
                    let extract_name ldi = ldi.qualid.id in
                    List.sort Stdlib.compare (List.map extract_name cdi)
                | _ -> assert false
              end
          | Deftypes.Tlink typ -> find_record_type_fields typ
          | _ -> assert false in
      match p.p_desc with
        | Ewildpat -> Pany
        | Etuplepat l -> Pconstr (Ttuple (List.length l), List.map inject l)
        | Evarpat _ -> Pany
        | Econstpat i -> Pconstr (Tconst i, [])
        | Eorpat (l, r) -> Por (inject l, inject r)
        | Ealiaspat (p, _) -> inject p
        | Econstr0pat s ->
            let variants = 
              let { t_desc = desc } = Types.typ_repr p.p_typ in
              match desc with
                | Deftypes.Tconstr(id, _, _) ->
                    find_variant_type_idents (Modname id)
                | _ -> assert false in
            Pconstr (Tconstr (source s, 0, variants), [])
        | Econstr1pat(s, l) ->
            let { t_desc = desc } = Types.typ_repr p.p_typ in
            Pconstr (Tconstr(source s, List.length l,
                             match desc with
                             | Deftypes.Tconstr(id, _, _) ->
                                 find_variant_type_idents (Modname id)
                             | _ -> assert false),
                     List.map inject l)
        | Etypeconstraintpat (p, _) -> inject p
        | Erecordpat l ->
            let ll = find_record_type_fields p.p_typ in
            let l' = List.map (fun (id, p) -> (source id, p)) l in
            (* Find the name of each field using type information *)
            let args = List.map
              (fun (id : string) ->
                 try let pat = List.assoc id l' in inject pat
                 with Not_found -> Pany) ll in
            Pconstr (Trecord ll, args)

    (* /!\ You should NEVER EVER use the result of eject for anything other than
       pretty-printing are other type-independent operations. Types are erased
       by the inject - eject pass, resulting one are bogus. /!\ *)
    (* Translation from tagged patterns is trivial. *)
    let rec eject internal_pat =
      let sensible_default pdesc = (* TODO: ask Marc *)
        { p_desc = pdesc; p_loc = Loc (0, 0);
          p_typ = { t_desc = Tvar; t_index = 0; t_level = 0 };
          p_caus = Defcaus.no_typ; p_init = Definit.no_typ } in
      match internal_pat with
        | Pany -> sensible_default Ewildpat
        | Por (l, r) -> sensible_default (Eorpat (eject l, eject r))
        | Pconstr (Ttuple _, l) ->
            sensible_default (Etuplepat (List.map eject l))
        | Pconstr (Tconst i, []) ->
            sensible_default (Econstpat i)
        | Pconstr (Tconstr (id, 0, _), []) ->
            sensible_default (Econstr0pat (Name id))
        | Pconstr (Tconstr (id, n, _), l) ->
            sensible_default (Econstr1pat (Name id, List.map eject l))
        | Pconstr (Trecord fl, l) ->
            let l =
              List.combine (List.map (fun s -> Name s) fl) (List.map eject l) in
            sensible_default (Erecordpat l)
        | _ -> assert false (* illformed pattern *)

  end

module C = PATTERN_CHECKER(LANG)

(** The main entry. Checks that pattern matching are exhaustive and warns *)
(** about redundancy. Returns [true] if the pattern matching is exhaustive *)
let check_match_handlers loc match_handlers =
  let partial_matching loc p =
    Typerrors.warning loc (Typerrors.Wpartial_matching(p)) in
  let display_redundant p =
    Typerrors.warning loc (Typerrors.Wmatch_unused(p)) in

  let patterns = List.map (fun { m_pat = pat } -> pat) match_handlers in
  let r = C.check patterns in

  Misc.optional_unit partial_matching loc r.C.not_matched;
  List.iter display_redundant r.C.redundant_patterns;
  match r.C.not_matched with | None -> true | Some _ -> false

(* check that a pattern is total. *)
let check_activate loc pat =
  let r = C.check [pat] in
  match r.C.not_matched with | None -> true | Some _ -> false
        
