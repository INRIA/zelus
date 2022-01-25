open Format
open Zlocation
open Zparsetree

module StringSet = Set.Make(struct type t = string let compare = compare end)

(* Collect free module identifiers in the a.s.t. *)

let add bv ln =
  match ln with
  | Modname {qual= s; id = _ } ->
      if not (StringSet.mem s !bv)
      then bv := StringSet.add s !bv
  | Name _ -> ()

let add_opt add_fn bv = function
  | None -> ()
  | Some x -> add_fn bv x

let add_default add_fn bv = function
  | Init v | Default v -> add_fn bv v

let rec add_size bv s =
  match s.desc with
  | Sconst _ -> ()
  | Sname id -> add bv id
  | Sop (_, s1, s2) -> add_size bv s1; add_size bv s2

let rec add_type_expr bv ty =
  match ty.desc with
  | Etypevar _ -> ()
  | Etypeconstr (id, tel) -> add bv id; List.iter (add_type_expr bv) tel
  | Etypetuple tl -> List.iter (add_type_expr bv) tl
  | Etypevec (ty, s) -> add_type_expr bv ty; add_size bv s
  | Etypefun (_, _, ty1, ty2) -> add_type_expr bv ty1; add_type_expr bv ty2
  | Etypefunrefinement(_, _, ty1, ty2, e) -> print_string "Refined arguments"; add_type_expr bv ty1; add_type_expr bv ty2

let rec add_interface bv i =
  match i.desc with
  | Einter_open s ->
    if not (StringSet.mem s !bv) then bv := StringSet.add s !bv
  | Einter_typedecl (_, _, tdl) -> add_type_decl bv tdl
  | Einter_constdecl (_, te) -> add_type_expr bv te

and add_type_decl bv td =
  match td.desc with
  | Eabstract_type -> ()
  | Eabbrev te -> add_type_expr bv te
  | Evariant_type _ -> ()
  | Erecord_type l -> List.iter (fun (_, te) -> add_type_expr bv te) l

and add_implem bv i =
  match i.desc with
  | Eopen s ->
    if not (StringSet.mem s !bv) then bv := StringSet.add s !bv;
  | Etypedecl (_, _, td) -> add_type_decl bv td
  | Econstdecl (_, _, e) -> add_exp bv e
  (*added here*)
  | Erefinementdecl (_,_,_,e) -> add_exp bv e
  | Eipopannotation (_,_,e) -> add_exp bv e
  | Efundecl (_, { f_args; f_body; _ }) ->
     List.iter (add_pattern bv) f_args;
     add_exp bv f_body

and add_exp bv exp =
  match exp.desc with
  | Evar l -> add bv l
  | Econst _ -> ()
  | Econstr0 c -> add bv c
  | Econstr1 (c, el) -> add bv c; List.iter (add_exp bv) el
  | Elast _ -> ()
  | Eapp (_, e, el) -> add_exp bv e; List.iter (add_exp bv) el
  | Eop (op, el) -> add_op bv op; List.iter (add_exp bv) el
  | Etuple el -> List.iter (add_exp bv) el
  | Erecord_access (e, id) -> add_exp bv e; add bv id
  | Erecord fields -> List.iter (add_field bv) fields
  | Erecord_with (e, fields) -> add_exp bv e; List.iter (add_field bv) fields
  | Etypeconstraint (e, ty) -> add_exp bv e; add_type_expr bv ty
  | Elet (_, pel, e) -> List.iter (add_eq bv) pel; add_exp bv e
  | Eseq (e1, e2) -> add_exp bv e1; add_exp bv e2
  | Eperiod _ -> ()
  (*added here*)
  | Eassume (e) -> add_exp bv e;
  (*added here
  | Emove (e) -> add_exp bv e;*)
  (*added here*)
  | Estore (cmd , key) -> ()
  (*added here*)
  | Eget (cm) -> ()
  | Ematch (e, mhl) -> add_exp bv e; List.iter (add_match_handler add_exp bv) mhl
  | Epresent (phl, edo) ->  List.iter (add_present_handler add_exp bv) phl; add_opt (add_default add_exp) bv edo
  | Eautomaton (shl, seo) -> List.iter (add_state_handler add_exp bv) shl; add_opt add_state_exp bv seo
  | Ereset (e1,e2) -> add_exp bv e1; add_exp bv e2
  | Eblock (eqsb, body) -> add_block add_eq_list bv eqsb; add_exp bv body

and add_op bv op =
  match op with
  | Efby | Eunarypre | Eifthenelse | Eminusgreater | Eup| Einitial | Edisc | (*added here*) Emove|(*added here*) Econtrol |(*added here*) Estr
  |(*added here*) Einp |(*added here*) Eoup | Etest | Eaccess | Eupdate | Econcat | Eatomic -> ()
  | Eslice (s1, s2) -> add_size bv s1; add_size bv s2
and add_field bv (lbl, e) = add bv lbl; add_exp bv e

and add_pattern bv pat =
  match pat.desc with
  | Etuplepat pl -> List.iter (add_pattern bv) pl
  | Evarpat _ -> ()
  | Ewildpat -> ()
  | Econstpat _ -> ()
  | Econstr0pat c -> add bv c
  | Econstr1pat (c, pl) -> add bv c; List.iter (add_pattern bv) pl
  | Ealiaspat (p, _) -> add_pattern bv p
  | Eorpat (p1, p2) -> add_pattern bv p1; add_pattern bv p2
  | Erecordpat pl -> List.iter (fun (lbl, p) -> add bv lbl; add_pattern bv p) pl
  | Etypeconstraintpat (p, ty) -> add_pattern bv p; add_type_expr bv ty

and add_eq bv eq =
  match eq.desc with
  | EQeq (p,e) -> add_pattern bv p; add_exp bv e
  | EQder (_, e, eo, phl) -> add_exp bv e; add_opt add_exp bv eo; List.iter (add_present_handler add_exp bv) phl
  | EQinit (_, e) | EQpluseq (_, e) -> add_exp bv e
  | EQnext (_, e, eo) -> add_exp bv e; add_opt add_exp bv eo
  | EQemit (_, eo) -> add_opt add_exp bv eo
  | EQautomaton (shl, seo) -> List.iter (add_state_handler add_eq_list bv) shl; add_opt add_state_exp bv seo
  | EQpresent (phl, bo) -> List.iter (add_present_handler (add_block add_eq_list) bv) phl; add_opt (add_block add_eq_list) bv bo
  | EQmatch (e, mhl) -> add_exp bv e; List.iter (add_match_handler (add_block add_eq_list) bv) mhl
  | EQifthenelse (e, bl, elsebl) ->
     add_exp bv e;
     add_block add_eq_list bv bl;
     add_opt (add_block add_eq_list) bv elsebl
  | EQand eqs | EQbefore eqs -> add_eq_list bv eqs
  (*added here
  | EQstore rob -> ()*)
  | EQreset (eql, e) -> List.iter (add_eq bv) eql; add_exp bv e
  | EQblock block -> add_block add_eq_list bv block
  | EQforall handler -> add_forall_handler bv handler

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

and add_statepat _bv sp =
  match sp.desc with
  | Estate0pat _ -> ()
  | Estate1pat _ -> ()

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
  fun a bv { desc = h; _ } ->
  add_statepat bv h.s_state;
  add_block a bv h.s_block;
  List.iter (add_escape bv) h.s_until;
  List.iter (add_escape bv) h.s_unless

and add_forall_handler bv { for_indexes; for_init; for_body; } =
  List.iter (add_index bv) for_indexes;
  List.iter (add_init bv) for_init;
  add_block add_eq_list bv for_body

and add_index bv index =
  match index.desc with
  | Einput (_, e) -> add_exp bv e
  | Eoutput (_, _) -> ()
  | Eindex (_, e1, e2) -> add_exp bv e1; add_exp bv e2

and add_init bv init =
  match init.desc with
  | Einit_last (_, e) -> add_exp bv e

let file traverse initial_structures file =
  let bv = ref initial_structures in
  List.iter (traverse bv) file;
  !bv

let source_file ?(initial_structures = StringSet.empty) source =
  file add_implem initial_structures source

let interface_file ?(initial_structures = StringSet.empty) interface =
  file add_interface initial_structures interface
