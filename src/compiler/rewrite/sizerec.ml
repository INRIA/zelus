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

(* Specialization of size functions *)

(* declarations [let rec f1<<n1,...>> = ... and fk<<<n1,...>> = ...] *)
(* are removed. Fresh functions are introduced for all specialized *)
(* applications with constant sizes, i.e., f<<s1,...>> where s1,..., are *)
(* integer constant *)

open Misc
open Location
open Ident
open Lident
open Global
open Zelus

(* unexpected error *)
let error loc message =
  Format.eprintf "%aError in pass sizerec %s\n"
    Location.output_location loc message;
  raise Misc.Error

(* fresh name *)
let fresh sf_id v_list =
  let name = (Ident.name sf_id) ^ "_" ^
               (List.fold_right (fun v rest -> (string_of_int v) ^ rest)
                  v_list "") in
  fresh name

(* memoization table; mapping [id -> (s1,...,sn) -> id_j] *)
(* where [s1,...,sn] are integer values *)
module Memo =
  Map.Make (struct type t = int list let compare = Stdlib.compare end)

(* a global table indexed by a qualified ident *)
module GlobalSizeFunTable =
  Map.Make(struct type t = Lident.qualident let compare = Stdlib.compare end)

type acc =
  { (* a map [f -> e] where [f] is the name of a size function definitions *)
    env_of_sizefun: sizefun Env.t;
    (* a map of sizes [id -> v] with [v] a positive integer *)
    env_of_sizes: int Env.t;
  }

and sizefun = 
{ (* size function: [sf_id <<n1,...>> = e] *)
    sizefun: Typinfo.sizefun;
    (* the list of specialized functions *)
    mutable sizefun_specialized: (Ident.t * Typinfo.exp) list;
    (* the memoization table which associate a fresh name [id] to (s1,...,sn) *)
    mutable sizefun_memo_table: Ident.t Memo.t;
    (* [sf_id] used or not in the code *)
    mutable sizefun_used: bool;
  }

(* global table for size functions: map [qualid -> { entry }] *)
let global_table = ref GlobalSizeFunTable.empty

let find_global_value loc lname =
  try
    let { qualid; info = { value_exp } } = Modules.find_value lname in
    (try
       GlobalSizeFunTable.find qualid !global_table
     with
       Not_found ->
        (* check that [value_exp] is a size function *)
        match value_exp with
        | Some(Vsizefun(sizefun)) ->
           let entry =
             { sizefun; sizefun_used = false;
               sizefun_specialized = [];
               sizefun_memo_table = Memo.empty } in
           global_table := GlobalSizeFunTable.add qualid entry !global_table;
           entry
       | Some(Vfun _) | None -> raise Not_found)
  with
    Not_found ->
     error loc
       ("no size function definition exist for" ^ (Lident.modname lname))

(* store a size function in the global symbol table *)
let set_global_sizefun loc qualid sizefun =
  try
    let entry = Modules.find_value (Modname qualid) in
    Global.set_value_exp entry (Vsizefun sizefun)
  with
    Not_found -> error loc "Unbound global identifier"

(* add an extra specialized version for [sf_id] to the global table *)
let add_global_specialized_sizefun loc qualid (sf_fresh_id, e) =
  try
    let { sizefun_specialized } as entry =
      GlobalSizeFunTable.find qualid !global_table in
    entry.sizefun_specialized <- (sf_fresh_id, e) :: sizefun_specialized
  with
    Not_found -> 
      error loc ("Unbound global identifier" ^ (Lident.qualidname qualid))

(* flush the table and generate a list of new global functions *)
let flush_global_specialized_sizefun p_impl_list =
  let get_specialized_sizefun
        qualid { sizefun_specialized } p_impl_list =
    let eq_list =
      List.map (fun (id, e) -> Aux.id_eq id e) sizefun_specialized in
    let d_names =
      List.map (fun (id, _) -> (Ident.name id, id)) sizefun_specialized in
    let l_decl = Aux.letdecl d_names (Aux.leq false eq_list) in
    (* add entry in the symbol table *)
    List.iter
      (fun (id, { e_info }) ->
        let ty = Typinfo.get_type e_info in
        Modules.add_value (Ident.name id)
          (Global.value_desc false (Deftypes.scheme ty)))
      sizefun_specialized;
    l_decl :: p_impl_list in
  GlobalSizeFunTable.fold get_specialized_sizefun !global_table p_impl_list

let empty = { env_of_sizefun = Env.empty; env_of_sizes = Env.empty }

(* given [f, { sf_id;... }] store it in [acc] *)
let add_sizefun ({ env_of_sizefun } as acc) ({ sf_id } as sizefun) =
  { acc with env_of_sizefun =
               Env.add sf_id { sizefun; sizefun_used = false;
                               sizefun_specialized = [];
                               sizefun_memo_table = Memo.empty }
                 env_of_sizefun  }

(* returns [{ sf_id; sf_id_list; sf_e }] associated [sf_id] in [acc] *)
let find_sizefun sf_id { env_of_sizefun } =
  Env.find_stop_if_unbound "Error in pass sizerec" sf_id env_of_sizefun

(* [sf_id] is used or not *)
let is_used sf_id env_of_sizefun =
  let { sizefun_used } = find_sizefun sf_id env_of_sizefun in sizefun_used

(* make [sf_id] to be used *)
let set_used sf_id ({ env_of_sizefun } as acc) =
  try
    let { sizefun_used } as entry = Env.find sf_id env_of_sizefun in
    entry.sizefun_used <- true;
    acc
  with
    Not_found -> acc

(* add an extra specialized version for [sf_id] *)
let add_specialized_sizefun ({ sizefun_specialized } as entry)
      (sf_fresh_id, e) acc =
  entry.sizefun_specialized <- (sf_fresh_id, e) :: sizefun_specialized;
  acc

let get_specialized_sizefun acc sizefun_specialized_list sf_id =
  let { sizefun_specialized } = find_sizefun sf_id acc in
  let leq_list =
    List.map (fun (id, e) -> Aux.leq false [Aux.id_eq id e])
      sizefun_specialized in
  leq_list @ sizefun_specialized_list

    
(* evaluation of size expressions *)
let size env ({ loc } as s) =
  let rec size { desc } =
    match desc with
    | Size_int(i) -> i
    | Size_var(id) -> Env.find id env
    | Size_frac { num; denom } -> size num / denom
    | Size_op(op, s1, s2) ->
       let v1 = size s1 and v2 = size s2 in
       match op with
       | Size_plus -> v1 + v2 | Size_minus -> v1 - v2 | Size_mult -> v1 * v2 in
  try
    size s
  with
    Not_found -> error loc "evaluation of size expressions"

let size_e env ({ e_loc } as e) =
  let rec size { e_desc; e_loc } =
    match e_desc with
    | Econst(Eint(i)) -> i
    | Evar(id) -> Env.find id env
    | Eapp { f = { e_desc = Eglobal { lname = Lident.Modname(qualid) } };
             arg_list = [e1; e2] } ->
       let v1 = size e1 and v2 = size e2 in
       if qualid = Initial.stdlib_name "+"
       then v1 + v2
       else if qualid = Initial.stdlib_name "-"
       then v1 - v2
       else if qualid = Initial.stdlib_name "*"
       then v1 * v2
       else if qualid = Initial.stdlib_name "/"
       then v1 / v2
       else raise Not_found
    | _ -> raise Not_found in
  try
    size e
  with
    Not_found -> error e_loc "evaluation of size expressions"

(* a generic function for [let leq in e] and [let leq in eq] *)
let let_in funs body_it acc ({ l_eq; l_loc } as leq) body =
  match Typing.eq_or_sizefun l_loc l_eq with
  | Either.Left _ ->
     let leq, acc = Mapfold.leq_it funs acc leq in
     let b, acc = body_it funs acc body in
     (Some leq, [], b), acc
  | Either.Right(sizefun_list) ->
     (* add entry [sf_id -> sizefun] for every element of the list *)
     let sf_id_list, acc =
       List.fold_left
         (fun (sf_id_list, acc) ({ sf_id } as sizefun) ->
           sf_id :: sf_id_list, add_sizefun acc sizefun)
         ([], acc) sizefun_list in
     (* compile the body *)
     let b, acc = body_it funs acc body in
     (* if one use of the [sf_id] appear in the body, the size function *)
     (* definitions are kept *)
     let used =
       List.fold_left
         (fun used sf_id ->
           used || (is_used sf_id acc)) false sf_id_list in
     (* get the list of specialized size functions generated during the *)
     (* treatment of [body] *)
     let sizefun_specialized_list =
       List.fold_left (get_specialized_sizefun acc) [] sf_id_list in
     (* specialized functions are stored in reverse order w.r.t *)
     (* the order they must be introduced *)
     let sizefun_specialized_list = List.rev sizefun_specialized_list in
     if used then
       (* keep the list of size function definitions *)
       (Some leq, sizefun_specialized_list, b), acc
     else
       (* remove them *)
       (None, sizefun_specialized_list, b), acc

(* a generic function to treat [match size] constructs. *)
(* [match size e with | (p_i -> eq_i)_i] and *)
(* [match size e with | (p_i -> e_i)_i] *)
let match_size_t loc funs body_it ({ env_of_sizes } as acc) v handlers =
  (* match a constant size [v] against a pattern [p] *)
  let pmatch v p =
    let open Monad.Opt in
    let rec pmatch env v { pat_desc } =
      match v, pat_desc with
      | _, Etypeconstraintpat(p, _) -> pmatch env v p
      | _, Evarpat(x) ->
         return (Env.add x v env)
      | _, Ewildpat -> return env
      | _, Ealiaspat(p, x) ->
         let* acc = pmatch env v p in
         return (Env.add x v env)
      | _, Eorpat(p1, p2) ->
         let env_opt = pmatch env v p1 in
         let env =
           match env_opt with
           | None -> pmatch env v p2
           | Some(env) -> return env in
         env
      | v1, Econstpat(Eint(v2)) when v1 = v2 -> return env
      | _ -> none in
    pmatch Env.empty v p in

  let rec match_rec handlers =
    match handlers with
    | [] -> error loc "pattern matching failure"
    | { m_pat; m_body } :: handlers ->
       let r = pmatch v m_pat in
       match r with
       | None ->
          (* this is not the good handler; try an other one *)
          match_rec handlers
       | Some(env_of_sizes_p) ->
          body_it funs
            { acc with env_of_sizes = Env.append env_of_sizes_p env_of_sizes }
            m_body in
  
  let body, acc = match_rec handlers in
  body, acc

let equation funs ({ env_of_sizes } as acc) ({ eq_desc; eq_loc } as eq) =
  match eq_desc with
  | EQlet({ l_eq } as leq, eq_let) ->
     let (leq_opt, sizefun_specialized_list, eq_let), acc =
       let_in funs Mapfold.equation_it acc leq eq_let in
     { eq with eq_desc =
                 Aux.opt_let_leq_in_eq leq_opt
                   (Aux.let_leq_list_in_eq
                      sizefun_specialized_list eq_let) },
     acc
  | EQmatch { is_size = true; e; handlers } ->
     let v = size_e env_of_sizes e in
     let eq, acc =
       match_size_t eq_loc funs Mapfold.equation_it acc v handlers in
     eq, acc
  | _ -> raise Mapfold.Fallback

(* compile a specialized size function and add a new definition *)
(* [sf_id = sf_e[v1/id1,...,vn/idn]] in [acc] *)
let sizefun funs
      ({ env_of_sizes } as acc) (sf_id, sf_id_list, v_list, sf_e) =
  let env_of_sizes =
    List.fold_left2
      (fun env_of_sizes sf_id v -> Env.add sf_id v env_of_sizes)
      env_of_sizes sf_id_list v_list in
  let sf_e, acc = Mapfold.expression_it funs { acc with env_of_sizes } sf_e in
  sf_e, acc

(* application [f<<s1,...,sn>>] where [s1,...] are integer constant *)
let sizeapp funs ({ env_of_sizes } as acc)
      ({ sizefun = { sf_id; sf_id_list; sf_e }; sizefun_memo_table } as entry)
      size_list =
  let v_list = List.map (size env_of_sizes) size_list in
  let id, acc =
    try
      Memo.find v_list sizefun_memo_table, acc
    with
      Not_found ->
        let sf_fresh_id = fresh sf_id v_list in
        (* add entry [v_list -> sf_fresh_id] to the memo table *)
        entry.sizefun_memo_table <-
          Memo.add v_list sf_fresh_id sizefun_memo_table;
        (* compile the specialized version of [sf_id] *)
        let sf_e, acc =
          sizefun funs acc (sf_id, sf_id_list, v_list, sf_e) in
        (* add the new function definition to the list of specialized size *)
        (* functions for [sf_id] *)
        let acc = add_specialized_sizefun entry (sf_fresh_id, sf_e) acc in
        sf_fresh_id, acc in
  id, acc

let size_t global_funs ({ env_of_sizes } as acc) ({ desc } as si) =
  match desc with
  | Size_var(id) ->
     (try { si with desc = Size_int(Env.find id env_of_sizes)}, acc
      with Not_found -> si, acc)
  | _ -> raise Mapfold.Fallback

let expression funs ({ env_of_sizefun; env_of_sizes } as acc) 
      ({ e_desc; e_loc } as e) =
  match e_desc with
  | Evar(x) ->
     (* replace [x] by its value if [x] is a size variable; otherwise *)
     (* mark it to be used if it is a size function *)
     let e, acc =
       try
         { e with e_desc = Econst(Eint(Env.find x env_of_sizes)) }, acc
       with Not_found ->
         e, set_used x acc in
     e, acc     
  | Elet({ l_eq } as leq, e_let) ->
     let (leq_opt, sizefun_specialized_list, e_let), acc =
       let_in funs Mapfold.expression_it acc leq e_let in
     { e with e_desc =
                Aux.opt_let_leq_in_e_desc leq_opt
                  (Aux.let_leq_list_in_e sizefun_specialized_list e_let) },
     acc
  | Esizeapp { f = { e_desc = Evar(f) }; size_list } ->
     (* [f <<s1,...>>] where the [s_i] are immediate values] *)
     (try
         let entry = Env.find f env_of_sizefun in
         let sf_fresh_id, acc = sizeapp funs acc entry size_list in
         Aux.var sf_fresh_id, acc
       with
         Not_found -> e, acc)
  | Esizeapp { f = { e_desc = Eglobal { lname }; e_loc }; size_list } ->
     (* [f <<s1,...>>] where the [s_i] are immediate values] *)
     (try
         let entry = find_global_value e_loc lname in
         let sf_fresh_id, acc = sizeapp funs acc entry size_list in
         Aux.global (Name(Ident.name sf_fresh_id)), acc
       with
         Not_found -> e, acc)
  | Ematch { is_size = true; e; handlers } ->
     let v = size_e env_of_sizes e in
     let e, acc =
       match_size_t e_loc funs Mapfold.expression_it acc v handlers in
     e, acc
  | _ -> raise Mapfold.Fallback

let set_index funs acc n =
  let _ = Ident.set n in n, acc
let get_index funs acc n = Ident.get (), acc

let letdecl funs acc (d_names, ({ l_eq; l_loc } as d_leq)) =
  match Typing.eq_or_sizefun l_loc l_eq with
  | Either.Left _ ->
     let d_leq, acc = Mapfold.leq_it funs acc d_leq in
     (d_names, d_leq), acc
  | Either.Right(sizefun_list) ->
     let sizefun_map = 
       List.fold_left
         (fun acc ({ sf_id } as sizefun) -> Env.add sf_id sizefun acc) 
         Env.empty sizefun_list in
     (* add entry [sf_id -> sizefun] for every element of the list *)
     (* into the global table *)
     let update_module_table d_names (name, m) =
       try
         let entry = Modules.find_value (Name name) in
         let sizefun = Env.find m sizefun_map in
         Global.set_value_exp entry
           (Global.Vsizefun(sizefun));
         (* entry [name, m] is removed from the list of defined names *)
         d_names
       with
         Not_found -> (name, m) :: d_names in
     let d_names = List.fold_left update_module_table [] d_names in
     (d_names, Aux.leq false []), acc

let open_t funs acc modname =
  Modules.open_module modname;
  modname, acc

let program genv p =
  let global_funs = { Mapfold.default_global_funs with size_t } in
  let funs =
    { Mapfold.defaults with
      global_funs; equation; expression; letdecl; open_t;
      set_index; get_index; } in
  let { p_impl_list } as p, _ =
    if !Misc.sizerec then Mapfold.program_it funs empty p else p, empty in
  (* remove empty declarations [let ()] *)
  let p_impl_list = List.filter Aux.not_empty_impl p_impl_list in
  (* flush specialized size function generated during the pass *)
  let sizefun_specialized_impl_list =
    flush_global_specialized_sizefun p_impl_list in
  { p with p_impl_list = sizefun_specialized_impl_list } 
