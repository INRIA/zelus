(* file: depend.ml *)

(* Warning: *)
(* This file is based on the original version of depend.ml *)
(* from the Objective Caml 3.10 distribution, INRIA, *)
(* then rewritten for ReactiveML by Louis Mandel *)

open Format
open Location
open Parsetree

module StringSet = Set.Make(struct type t = string let compare = compare end)

(* Collect free module identifiers in the a.s.t. *)

let free_structure_names = ref StringSet.empty

let rec add bv ln =
  match ln with
  | Modname {qual= s; id = _ } ->
      if not (StringSet.mem s bv)
      then free_structure_names := StringSet.add s !free_structure_names
  | Name _ -> ()

let add_opt add_fn bv = function
  | None -> ()
  | Some x -> add_fn bv x

let rec add_type_expr bv ty =
  match ty.desc with
  | Etypevar _ -> ()
  | Etypeconstr (id, tel) -> add bv id; List.iter (add_type_expr bv) tel
  | Etypetuple tl -> List.iter (add_type_expr bv) tl

let rec add_interface bv i =
  match i.desc with
  | Einter_open s ->
    if not (StringSet.mem s bv)
    then free_structure_names := StringSet.add s !free_structure_names;
    bv
  | Einter_typedecl (_, _, tdl) -> add_type_decl bv tdl; bv
  | Einter_constdecl (_, te) -> add_type_expr bv te; bv
  | Einter_fundecl (_, ts) -> add_type_sig bv ts; bv

and add_signature bv = function
  | [] -> ()
  | item :: rem -> add_signature (add_interface bv item) rem

and add_type_decl bv td =
  match td with
  | Eabstract_type -> ()
  | Eabbrev te -> add_type_expr bv te
  | Evariant_type _ -> ()
  | Erecord_type l -> List.iter (fun (_, te) -> add_type_expr bv te) l

and add_implem bv i =
  match i.desc with
  | Eopen s ->
    if not (StringSet.mem s bv)
    then free_structure_names := StringSet.add s !free_structure_names;
    bv
  | Etypedecl (_, _, td) -> add_type_decl bv td; bv
  | Econstdecl (_, e) -> add_exp bv e; bv
  | Efundecl (_, _, _, pl, e) -> List.iter (add_pattern bv) pl; add_exp bv e;bv

and add_use_file bv top_phrs =
  ignore (List.fold_left add_implem bv top_phrs)

and add_type_sig bv ts =
  List.iter (add_type_expr bv) ts.sig_inputs;
  add_type_expr bv ts.sig_output


and add_exp bv exp =
  match exp.desc with
  | Evar l -> add bv l
  | Econst _ -> ()
  | Econstr0 c -> add bv c
  | Elast _ -> ()
  | Eapp (op, el) -> add_op bv op; List.iter (add_exp bv) el
  | Etuple el -> List.iter (add_exp bv) el
  | Erecord_access (e, id) -> add_exp bv e; add bv id
  | Erecord lblel -> List.iter (fun (lbl, e) -> add bv lbl; add_exp bv e) lblel
  | Etypeconstraint (e, ty) -> add_exp bv e; add_type_expr bv ty
  | Elet (_, pel, e) -> List.iter (add_eq bv) pel; add_exp bv e
  | Eseq (e1, e2) -> add_exp bv e1; add_exp bv e2
  | Eperiod _ -> ()
  | Ematch (e, mhl) -> add_exp bv e; List.iter (add_match_handler add_exp bv) mhl
  | Epresent (phl, eo) ->  List.iter (add_present_handler add_exp bv) phl; add_opt add_exp bv eo
  | Eautomaton (shl, seo) -> List.iter (add_state_handler add_exp bv) shl; add_opt add_state_exp bv seo
  | Ereset (e1,e2) -> add_exp bv e1; add_exp bv e2

and add_op bv op =
  match op with
  | Eop n -> add bv n
  | Efby | Eunarypre | Eifthenelse | Eminusgreater | Eup | Einitial | Edisc | Eon | Etest -> ()

and add_pattern bv pat =
  match pat.desc with
  | Etuplepat pl -> List.iter (add_pattern bv) pl
  | Evarpat _ -> ()
  | Ewildpat -> ()
  | Econstpat _ -> ()
  | Econstr0pat c -> add bv c
  | Ealiaspat (p, _) -> add_pattern bv p
  | Eorpat (p1, p2) -> add_pattern bv p1; add_pattern bv p2
  | Erecordpat pl -> List.iter (fun (lbl, p) -> add bv lbl; add_pattern bv p) pl
  | Etypeconstraintpat (p, ty) -> add_pattern bv p; add_type_expr bv ty

and add_eq bv eq =
  match eq.desc with
  | EQeq (p,e) -> add_pattern bv p; add_exp bv e
  | EQder (_, e, eo, phl) -> add_exp bv e; add_opt add_exp bv eo; List.iter (add_present_handler add_exp bv) phl
  | EQinit (p, e, eo) -> add_pattern bv p; add_exp bv e; add_opt add_exp bv eo
  | EQnext (p, e, eo) -> add_pattern bv p; add_exp bv e; add_opt add_exp bv eo
  | EQemit (_, eo) -> add_opt add_exp bv eo
  | EQautomaton (shl, seo) -> List.iter (add_state_handler add_eq_list bv) shl; add_opt add_state_exp bv seo
  | EQpresent (phl, bo) -> List.iter (add_present_handler (add_block add_eq_list) bv) phl; add_opt (add_block add_eq_list) bv bo
  | EQmatch (e, mhl) -> add_exp bv e; List.iter (add_match_handler (add_block add_eq_list) bv) mhl
  | EQreset (eql, e) -> List.iter (add_eq bv) eql; add_exp bv e

and add_eq_list bv le =
  List.iter (add_eq bv) le

and add_block: 'a. ('b -> 'a -> unit) -> 'b -> 'a block -> unit =
  fun a bv b ->
  let bb = b.desc in
  List.iter (add_local bv) bb.b_locals;
  a bv bb.b_body

and add_local bv l =
  let (_, eql) = l.desc in
  List.iter (add_eq bv) eql

and add_statepat bv sp =
  match sp.desc with
  | Estate0pat _ -> ()
  | Estate1pat (_, pl) -> List.iter (add_pattern bv) pl

and add_state_exp bv se =
  match se.desc with
  | Estate0 _ -> ()
  | Estate1 (_, el) -> List.iter (add_exp bv) el

and add_escape bv e =
  add_scondpat bv e.e_cond;
  add_opt (add_block add_eq_list) bv e.e_block;
  add_state_exp bv e.e_next_state

and add_scondpat bv scp =
  match scp.desc with
  | Econdand (s1, s2) -> add_scondpat bv s1; add_scondpat bv s2
  | Econdor (s1, s2) -> add_scondpat bv s1; add_scondpat bv s2
  | Econdexp e -> add_exp bv e
  | Econdon (s, e) -> add_scondpat bv s; add_exp bv e
  | Econdpat (e, p) -> add_exp bv e; add_pattern bv p

and add_match_handler: 'a. ('b -> 'a -> unit) -> 'b -> 'a match_handler -> unit =
  fun a bv h ->
  add_pattern bv h.m_pat;
  a bv h.m_body

and add_present_handler: 'a. ('b -> 'a -> unit) -> 'b -> 'a present_handler -> unit =
  fun a bv h ->
  add_scondpat bv h.p_cond;
  a bv h.p_body

and add_state_handler: 'a. ('b -> 'a -> unit) -> 'b -> 'a state_handler -> unit =
  fun a bv h ->
  add_statepat bv h.s_state;
  add_block a bv h.s_block;
  List.iter (add_escape bv) h.s_until;
  List.iter (add_escape bv) h.s_unless
