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

(* Functions to build terms *)
(* Invariant: writes for equations must be correct *)

open Misc
open Location
open Zelus
open Ident
open Lident
open Initial
open Deftypes

module Write =  Write.Make(Typinfo)

(* Constant expressions - simple and sufficient condition for [e] to be *)
(* constant *)
let rec const { e_desc } =
  match e_desc with
  | Econst _ | Econstr0 _ | Eglobal _ -> true
  | Etuple(e_list) -> List.for_all const e_list
  | Erecord(qual_e_list) ->
     List.for_all (fun { arg } -> const arg) qual_e_list
  | Erecord_access { arg } -> const arg
  | _ -> false

let defnames eq_list =
  List.fold_left (fun acc { eq_write } -> Defnames.union eq_write acc)
    Defnames.empty eq_list

let desc e = e.desc
let make x = { desc = x; loc = no_location }

let emake desc : Typinfo.exp =
  { e_desc = desc; e_loc = no_location; e_info = Typinfo.no_info }
let pmake desc : Typinfo.pattern =
  { pat_desc = desc; pat_loc = no_location; pat_info = Typinfo.no_info }

(* annotate with a type *)
let e_with_type ({ e_info } as e) ty =
  { e with e_info = Typinfo.set_type e_info ty }
let p_with_type ({ pat_info } as p) ty =
  { p with pat_info = Typinfo.set_type pat_info ty }

let global lname = emake (Eglobal { lname = lname })
let const c = emake (Econst c)
let constr0 lname = emake (Econstr0 { lname })
let constr1 lname arg_list = emake (Econstr1 { lname; arg_list })
let evoid : Typinfo.exp = const Evoid
let efalse : Typinfo.exp = const (Ebool(false))
let etrue : Typinfo.exp = const (Ebool(true))
let truepat = pmake (Econstpat(Ebool(true)))
let falsepat = pmake (Econstpat(Ebool(false)))
let wildpat = pmake (Ewildpat)
let zero : Typinfo.exp = emake (Econst(Efloat(0.0)))
let one = emake (Econst(Efloat(1.0)))
let minus_one = emake (Econst(Efloat(-1.0)))
let infinity : Typinfo.exp =
  global (Modname(Initial.stdlib_name "infinity"))
let tuplepat pat_list = pmake (Etuplepat(pat_list))
let tuple e_list = emake (Etuple(e_list))
let record l_list e_list =
  emake (Erecord(List.map2 (fun label arg -> { label; arg }) l_list e_list))
let ifthenelse e e_true e_false =
  emake (Eop(Eifthenelse, [e_true; e_false]))

let result_e e = 
  { r_desc = Exp(e); r_loc = no_location; r_info = Typinfo.no_info }

let is_empty { eq_desc } =
  match eq_desc with | EQempty -> true | _ -> false

(* remove empty declarations [let ()] *)
let not_empty_impl { desc } = match desc with
  | Eletdecl { d_leq = { l_eq } } when is_empty l_eq -> false | _ -> true

let letdecl d_names d_leq = make (Eletdecl { d_names; d_leq })

let eqmake w desc =
  { eq_desc = desc; eq_loc = no_location; eq_write = w;
    eq_safe = true; eq_index = -1 }

let pat_make x =
  { pat_desc = Evarpat(x); pat_loc = no_location; pat_info = Typinfo.no_info }

let eq_make p e : Typinfo.eq =
  let w = { Defnames.empty with dv = Write.fv_pat S.empty p } in
  eqmake w (EQeq(p, e))

let id_eq id e =
  let w = Defnames.singleton id in
  eqmake w (EQeq(pat_make id, e))

let emit_id_eq id e =
  let w = Defnames.singleton id in
  eqmake w (EQemit(id, Some e))

let eq_empty () = eqmake Defnames.empty EQempty

let wildpat_eq e =
  eqmake Defnames.empty (EQeq(wildpat, e))

let eq_init id e : Typinfo.eq =
  let open Defnames in
  eqmake { empty with di = Ident.S.singleton id } (EQinit(id, e))

let eq_der id e =
  let w = { Defnames.empty with der = S.singleton id } in
  eqmake w (EQder { id; e; e_opt = None; handlers = [] })

let eq_and ordered eq1 eq2 =
  let w = Defnames.union eq1.eq_write eq2.eq_write in
  match eq1.eq_desc, eq2.eq_desc with
  | (EQempty, _) -> eq2 | (_, EQempty) -> eq1
  | EQand { ordered = ord1; eq_list = eq_list1 },
    EQand { ordered = ord2; eq_list = eq_list2 }
       when (ord1 = ord2) && (ord1 = ordered) ->
     eqmake w (EQand { ordered = ord1; eq_list = eq_list1 @ eq_list2 })
  | (EQand { ordered = ord; eq_list = eq_list1 }, _)
       when ord = ordered ->
     eqmake w (EQand { ordered = ord; eq_list = eq2 :: eq_list1 })
  | _, EQand { ordered = ord; eq_list = eq_list2 }
    when ord = ordered ->
     eqmake w (EQand { ordered = ord; eq_list = eq1 :: eq_list2 })
  | _ -> eqmake w (EQand { ordered = ordered; eq_list = [eq1; eq2] })

let rec par_t ordered eq_list =
  match eq_list with
  | [] -> eq_empty ()
  | eq :: eq_list ->
     eq_and ordered eq (par_t ordered eq_list)

let eq_and eq1 eq2 = eq_and false eq1 eq2
let seq eq_list = par_t true eq_list
let par eq_list = par_t false eq_list

let set_loc_if_not_empty loc eq = 
  if is_empty eq then { eq with eq_loc = loc } else eq

let init_vardec id var_is_last var_init var_default var_init_in_eq = 
  { var_name = id; var_is_last; var_init; var_default; var_clock = false;
    var_typeconstraint = None; var_loc = no_location; var_init_in_eq;
    var_info = Typinfo.no_info }

let vardec id var_is_last var_init var_default =
  init_vardec id var_is_last var_init var_default false

let id_vardec id = vardec id false None None

let env_of s = S.fold (fun n acc -> Env.add n Typinfo.no_ienv acc) s Env.empty
  
let block_make vardec_list eq_list =
  let b_body =
    match eq_list with
    | [] -> eq_empty ()
    | [eq] -> eq
    | _ -> par eq_list in
  let b = { b_vars = vardec_list; b_env = Env.empty; b_loc = no_location;
            b_write = Defnames.empty; b_body } in
  let w = defnames eq_list in
  let def = List.fold_left
              (fun acc { var_name } -> S.add var_name acc) S.empty
              vardec_list in
  let w = Defnames.diff w def in
  let b_env = env_of def in
  { b with b_write = w; b_env }

let block_empty () = block_make [] []

let eq_reset eq e = eqmake eq.eq_write (EQreset(eq, e))
let eq_match is_total e handlers =
  let w = List.fold_left
            (fun acc { m_body = { eq_write } } -> Defnames.union eq_write acc)
            Defnames.empty handlers in
  eqmake w (EQmatch { is_size = false; is_total; e; handlers })
let eq_present handlers default_opt =
  let w = List.fold_left
            (fun acc { p_body = { eq_write } } -> Defnames.union eq_write acc)
            Defnames.empty handlers in
  let w =
    match default_opt with
    | NoDefault -> w | Init(eq) | Else(eq) -> Defnames.union eq.eq_write w in
  eqmake w (EQpresent { handlers; default_opt })
    
let match_handler p b =
  { m_pat = p; m_body = b; m_env = env_of (Write.fv_pat S.empty p);
    m_reset = false; m_zero = false; m_loc = no_location }

let eq_ifthenelse e eq_true eq_false =
  let w = Defnames.union eq_true.eq_write eq_false.eq_write in
  eqmake w (EQif { e; eq_true; eq_false })

let eq_ifthen e eq_true =
  eq_ifthenelse e eq_true (eq_empty ())

let rec let_leq_list_in_eq leq_list eq =
  match leq_list with
  | [] -> eq
  | leq :: leq_list -> let_leq_in_eq leq (let_leq_list_in_eq leq_list eq)

and let_leq_in_eq ({ l_eq } as leq) eq =
  if is_empty l_eq then eq else eqmake eq.eq_write (EQlet(leq, eq))

let let_leq_in_eq_loc eq_loc leq eq =
  { (let_leq_in_eq leq eq) with eq_loc }

let opt_let_leq_in_eq leq_opt eq =
  match leq_opt with | None -> eq.eq_desc | Some(leq) -> EQlet(leq, eq)

let leq l_rec eq_list =
  { l_kind = Kany; l_rec; l_eq = par eq_list; l_loc = no_location;
    l_env = env_of (Defnames.names S.empty (defnames eq_list)); }

let let_leq_in_e ({ l_eq } as leq) e =
  if is_empty l_eq then e else emake (Elet(leq, e))
let let_leq_in_e_loc e_loc ({ l_eq } as leq) e =
  { (let_leq_in_e leq e) with e_loc }

let rec let_leq_list_in_e leq_list e =
  match leq_list with
  | [] -> e | leq :: leq_list -> let_leq_in_e leq (let_leq_list_in_e leq_list e)

let opt_let_leq_in_e l_opt e =
  match l_opt with | None -> e | Some(leq) -> let_leq_in_e leq e

let opt_let_leq_in_e_desc l_opt e =
  match l_opt with | None -> e.e_desc | Some(l) -> Elet(l, e)

let let_eq_list_in_e l_rec eq_list e =
  match eq_list with [] -> e | _ -> let_leq_in_e (leq l_rec eq_list) e
let let_eq_list_in_eq l_rec eq_list eq =
  match eq_list with [] -> eq | _ -> let_leq_in_eq (leq l_rec eq_list) eq

let pat_of_vardec_make { var_name } = pat_make var_name

let pat_of_vardec_list_make vardec_list =
  match vardec_list with
  | [] -> pmake Ewildpat
  | [v] -> pat_of_vardec_make v
  | _ -> pmake (Etuplepat(List.map pat_of_vardec_make vardec_list))

let match_f_arg_with_arg f_arg arg =
  let p = pat_of_vardec_list_make f_arg in
  eq_make p arg

let eq_local b = eqmake b.b_write (EQlocal(b))

let eq_local_vardec vardec_list eq_list =
  match vardec_list, eq_list with
  | _, [] -> eq_empty ()
  | [], _ -> par eq_list
  | _ -> eq_local (block_make vardec_list eq_list)

let returns_of_vardec_make { var_name } = emake (Evar(var_name))

let returns_of_vardec_list_make vardec_list =
  match vardec_list with
  | [] -> emake (Econst(Evoid))
  | _ -> emake (Etuple(List.map returns_of_vardec_make vardec_list))

let e_present handlers default_opt =
   emake (Epresent { handlers; default_opt })
let e_match is_total e handlers =
  emake (Ematch { is_size = false; is_total; e; handlers })

let local_in_e b e = emake (Elocal(b, e))

let local_vardec_in_e vardec_list eq_list e =
  match vardec_list, eq_list with
  | (_, []) -> e
  | [], _ -> let_eq_list_in_e true eq_list e
  | _ -> local_in_e (block_make vardec_list eq_list) e

let eq_ifthen e eq_true =
  eq_ifthenelse e eq_true (eq_empty ())

let rec orpat pat_list =
  match pat_list with
    | [] -> assert false
    | [pat] -> pat
    | pat :: pat_list -> pmake (Eorpat(pat, orpat pat_list))

let varpat name = pmake (Evarpat(name))
let var name = emake (Evar(name))

let pair e1 e2 =  emake (Etuple([e1; e2]))
let pairpat p1 p2 = pmake (Etuplepat([p1; p2]))

let patalias p n = pmake (Ealiaspat(p, n))
let last id = emake (Elast { copy = true; id })
let last_star id = emake (Elast { copy = false; id })
let float v = emake (Econst(Efloat(v)))
let bool v = emake (Econst(Ebool(v)))

let global_in_stdlib lname = global (Modname(Initial.stdlib_name lname))

let unop op e =
  emake (Eapp { is_inline = false; f = global_in_stdlib op; arg_list = [e] })
let binop op e1 e2 =
  emake (Eapp { is_inline = false; f = global_in_stdlib op;
                arg_list = [e1;e2] })

let plus e1 e2 = binop "+." e1 e2
let minus e1 e2 = binop "-." e1 e2
let diff e1 e2 = binop "<>" e1 e2
let or_op e1 e2 = binop "||" e1 e2
let and_op e1 e2 = binop "&&" e1 e2
let on_op e1 e2 = binop "on" e1 e2
let min_op e1 e2 = binop "min" e1 e2
let greater_or_equal e1 e2 = binop ">=" e1 e2
let greater e1 e2 = binop ">" e1 e2
let up e = emake (Eop(Eup { is_zero = true }, [e]))
let up_b e = emake (Eop(Eup { is_zero = false }, [e]))
let pre e = emake (Eop(Eunarypre, [e]))
let minusgreater e1 e2 = emake (Eop(Eminusgreater, [e1;e2]))
let fby e1 e2 = emake (Eop(Efby, [e1;e2]))
let ifthenelse e1 e2 e3 =
  emake (Eop(Eifthenelse, [e1;e2;e3]))
let horizon e = emake (Eop(Ehorizon { is_zero = true }, [e]))
let horizon_f e = emake (Eop(Ehorizon { is_zero = false }, [e]))

let sgn e =
  ifthenelse (greater e zero) one minus_one
let record_access arg label = emake (Erecord_access { arg; label })
    
(* introduce a hidden state variable *)
let new_hidden_state_variable m (t_sort, t_typ) env =
  Env.add m { t_path = Pkind(Tnode(Tcont));
              t_sort;
              t_tys = Deftypes.scheme t_typ } env

let major_entry m env =
  new_hidden_state_variable m (Deftypes.major (), Initial.typ_bool) env
let time_entry m env =
  new_hidden_state_variable m (Deftypes.time (), Initial.typ_float) env

exception Return of Ident.t

let get_hidden_state_variable sort hidden_env =
  let find x entry =
    match entry with
    | { t_sort = Sort_mem { m_mkind = Some(s) } } when s = sort ->
       raise (Return(x))
    | _ -> () in
  try
    Env.iter find hidden_env; None
  with
  | Return(x) -> Some(x)

