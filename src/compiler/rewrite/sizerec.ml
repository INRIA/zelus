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

(* declarations [let [rec] f1<<n1,...>> = ... and fk<<<n1,...>> = ...] *)
(* are removed. Fresh functions are introduced for all specialized *)
(* applications with constant sizes, i.e., f<<s1,...>> where s1,..., are *)
(* (size) integer constants *)

open Misc
open Location
open Ident
open Lident
open Global
open Zelus

(* unexpected error during the pass *)
let error loc message =
  Format.eprintf "%aError in pass sizerec %s:\n"
    Location.output_location loc message;
  raise Misc.Error

(* create a fresh name *)
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

type env =
  { (* a map [f -> e] where [f] is the name of a size function definition *)
    env_of_sizefun: sizefun Env.t Lazy.t;
    (* a map of sizes [id -> v] with [v] a positive integer *)
    env_of_sizes: int Env.t }

and sizefun = 
{ (* size function: [sf_id <<n1,...>> = e] *)
    sizefun_definition: Typinfo.sizefun;
    (* the memoization table which associate a fresh name [id] to (s1,...,sn) *)
    mutable sizefun_memo_table: Ident.t Memo.t;
    (* [sf_id] used or not in the code *)
    mutable sizefun_used: bool;
    (* the environment for free variables *)
    sizefun_env: env;
    (* is-it a global value or not? *)
    sizefun_is_global: bool;
  }

type acc =
  { (* environment for free variables *)
    env: env;
    (* the list of specialized functions that are generated during the pass *)
    (* the latest is added on the top of the list *)
    specialized_sizefun_list: (Ident.t * Typinfo.exp) list;
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
        let entry sizefun env =
          { sizefun_definition = sizefun;
            sizefun_used = false;
            sizefun_memo_table = Memo.empty;
            sizefun_env =
              { env_of_sizefun = env; env_of_sizes = Env.empty };
            sizefun_is_global = true } in
        (* check that [value_exp] is a size function *)
        match value_exp with
        | None -> raise Not_found
        | Some(v) ->
           let entry =
             match v with
             | Vfun _ -> raise Not_found
             | Vsizefun(sizefun) ->
                let entry = entry sizefun (lazy Env.empty) in
                entry
             | Vsizefunrec(sizefun, f_to_exp_env) ->
                let rec env_of_sizefun =
                  lazy
                    (Env.map (fun sizefun -> entry sizefun env_of_sizefun) 
                       f_to_exp_env) in
                entry sizefun env_of_sizefun in
           global_table := GlobalSizeFunTable.add qualid entry !global_table;
           entry)
  with
    Not_found ->
    error loc
      ("no size function definition exist for " ^ (Lident.modname lname))

(* store a size function in the global symbol table *)
let set_global_sizefun loc qualid sizefun =
  try
    let entry = Modules.find_value (Modname qualid) in
    Global.set_value_exp entry (Vsizefun sizefun)
  with
    Not_found -> error loc "Unbound global identifier"

(* flush the global table of new function definitions *)
let flush_global_specialized_sizefun { specialized_sizefun_list } p_impl_list =
  let one_letdecl p_impl_list (id, ({ e_info } as e)) =
    (* returns a global declaration [let id = ...] *)
    let l_decl = 
      Aux.letdecl [Ident.name id, id] (Aux.leq false [Aux.id_eq id e]) in
    let ty = Typinfo.get_type e_info in
    (* add entry in the symbol table *)
    Modules.add_value (Ident.name id)
      (Global.value_desc false (Deftypes.scheme ty));
    l_decl :: p_impl_list in
  List.fold_left one_letdecl p_impl_list specialized_sizefun_list

let empty_env = { env_of_sizefun = lazy Env.empty; env_of_sizes = Env.empty }
let empty = { env = empty_env; specialized_sizefun_list = [] }

(* given [f, { sf_id;... }] store it in [acc] *)
let add_sizefun_list 
      is_rec sizefun_list ({ env_of_sizefun; env_of_sizes } as env) =
  (* add a single entry *)
  let add_one_sizefun env_of_sizefun_rec env_of_sizefun ({ sf_id } as sizefun) =
    Env.add sf_id
      { sizefun_definition = sizefun; sizefun_used = false;
        sizefun_memo_table = Memo.empty; 
        sizefun_env = { env_of_sizefun = env_of_sizefun_rec; env_of_sizes };
      sizefun_is_global = false }
      env_of_sizefun in
  (* add a list of entries that are possibly recursively defined *)
  let rec env_of_sizefun_rec =
    lazy 
      (List.fold_left 
         (add_one_sizefun 
            (if is_rec then env_of_sizefun_rec else env_of_sizefun))
            (Lazy.force env_of_sizefun)
            sizefun_list) in
  { env with env_of_sizefun = env_of_sizefun_rec }

(* [sf_id] is used or not *)
let is_used loc sf_id { env = { env_of_sizefun } } =
  (* returns [{ sf_id; sf_id_list; sf_e }] associated [sf_id] in [acc] *)
  let find_sizefun sf_id env_of_sizefun =
    try
      Env.find sf_id env_of_sizefun
    with
    | Not_found -> error loc ("Unbound variable" ^ (Ident.name sf_id)) in

  let { sizefun_used } = find_sizefun sf_id (Lazy.force env_of_sizefun) in
  sizefun_used

(* make [sf_id] to be used *)
let set_used sf_id ({ env = { env_of_sizefun } } as acc) =
  try
    let { sizefun_used } as entry = Env.find sf_id (Lazy.force env_of_sizefun) in
    entry.sizefun_used <- true;
    acc
  with
    Not_found -> acc

(* add an extra specialized version for [sf_fresh_id] *)
let add_specialized_sizefun
      ({ specialized_sizefun_list } as acc) (sf_fresh_id, e) =
  { acc with specialized_sizefun_list =
               (sf_fresh_id, e) :: specialized_sizefun_list }

let flush_leq_list_of { specialized_sizefun_list } =
  (* the result is reversed *)
  List.fold_left (fun acc (id, e) -> Aux.leq false [Aux.id_eq id e] :: acc)
    [] specialized_sizefun_list
 
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
let let_in funs body_it ({ env; specialized_sizefun_list } as acc)
      ({ l_rec; l_eq; l_loc } as leq) body =
  match Typing.eq_or_sizefun l_loc l_eq with
  | Either.Left _ ->
     let leq, acc = Mapfold.leq_it funs acc leq in
     let b, acc = body_it funs acc body in
     (Some leq, [], b), acc
  | Either.Right(sizefun_list) ->
     (* add entry [sf_id -> sizefun] for every element of the list *)
     let sf_id_list =
       List.fold_left (fun sf_id_list { sf_id } -> sf_id :: sf_id_list)
         [] sizefun_list in
     let env = add_sizefun_list l_rec sizefun_list env in
     (* compile the body *)
     let b, acc = body_it funs { acc with env } body in
     (* if one use of the [sf_id] appear in the body, the size function *)
     (* definitions are kept *)
     let used =
       List.fold_left
         (fun used sf_id ->
           used || (is_used l_loc sf_id acc)) false sf_id_list in
     (* get the list of specialized size functions generated during the *)
     (* treatment of [body] *)
     let new_sizefun_specialized_list = flush_leq_list_of acc in
     (* set the list of specialized size function to what it was *)
     (* before entering the let/in block *)
     let acc = { acc with specialized_sizefun_list } in
     if used then
       (* keep the list of size function definitions *)
       (Some leq, new_sizefun_specialized_list, b), acc
     else
       (* remove them *)
       (None, new_sizefun_specialized_list, b), acc

(* a generic function to treat [match size] constructs. *)
(* [match size e with | (p_i -> eq_i)_i] and *)
(* [match size e with | (p_i -> e_i)_i] *)
let match_size_t loc funs body_it
      ({ env = ({ env_of_sizes } as env) } as acc) v handlers =
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
            { acc with env =
                         { env with
                           env_of_sizes = Env.append env_of_sizes_p env_of_sizes
            } } m_body in
  
  let body, acc = match_rec handlers in
  body, acc

let equation funs
      ({ env = ({ env_of_sizes } as env) } as acc) ({ eq_desc; eq_loc } as eq) =
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
let sizefun funs ({ env = ({ env_of_sizes } as env) } as acc)
      (sf_id, sf_id_list, v_list, sf_e) =
  let env_of_sizes =
    List.fold_left2
      (fun env_of_sizes sf_id v -> Env.add sf_id v env_of_sizes)
      env_of_sizes sf_id_list v_list in
  let sf_e, acc =
    Mapfold.expression_it funs { acc with env = { env with env_of_sizes } } sf_e in
  sf_e, acc

(* application [f<<s1,...,sn>>] where [s1,...] are integer constant *)
let sizeapp funs ({ env; specialized_sizefun_list } as acc)
      ({ sizefun_definition = { sf_id; sf_id_list; sf_e };
         sizefun_memo_table; 
         sizefun_env;
         sizefun_is_global } as entry)
      v_list =
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
        (* for that, take the environment [sizefun_env] of the closure *)
        let sf_e, acc =
          sizefun funs { acc with env = sizefun_env }
            (sf_id, sf_id_list, v_list, sf_e) in
        (* add the new function definition to the list of specialized size *)
        (* functions. The current environment is the on at the entry *)
        (* of [sizeapp] *)
        let acc = add_specialized_sizefun { acc with env } (sf_fresh_id, sf_e) in
        sf_fresh_id, acc in
  sizefun_is_global, id, acc

let size_t global_funs ({ env = { env_of_sizes } } as acc) ({ desc } as si) =
  match desc with
  | Size_var(id) ->
     (try { si with desc = Size_int(Env.find id env_of_sizes)}, acc
      with Not_found -> si, acc)
  | _ -> raise Mapfold.Fallback

let expression funs ({ env = { env_of_sizefun; env_of_sizes } } as acc) 
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
         let entry = Env.find f (Lazy.force env_of_sizefun) in
         let v_list = List.map (size env_of_sizes) size_list in
         let is_global, sf_fresh_id, acc = sizeapp funs acc entry v_list in
         let id = if is_global then  Aux.global (Name(Ident.name sf_fresh_id))
                  else Aux.var sf_fresh_id in
         id, acc
       with
         Not_found -> e, acc)
  | Esizeapp { f = { e_desc = Eglobal { lname }; e_loc }; size_list } ->
     (* [f <<s1,...>>] where the [s_i] are immediate values] *)
     (try
         let entry = find_global_value e_loc lname in
         let v_list = List.map (size env_of_sizes) size_list in
         let is_global, sf_fresh_id, acc = sizeapp funs acc entry v_list in
         let id = if is_global then  Aux.global (Name(Ident.name sf_fresh_id))
                  else Aux.var sf_fresh_id in
         id, acc
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

let letdecl funs acc (d_names, ({ l_rec; l_eq; l_loc } as d_leq)) =
  match Typing.eq_or_sizefun l_loc l_eq with
  | Either.Left _ ->
     let d_leq, acc = Mapfold.leq_it funs acc d_leq in
     (d_names, d_leq), acc
  | Either.Right(sizefun_list) ->
     (* make and entry [sf_id -> sizefun] for every element of the list *)
     let f_to_exp_env =
       List.fold_left 
         (fun env_of_sizefun_defs ({ sf_id } as sizefun) -> 
           Env.add sf_id sizefun env_of_sizefun_defs)
         Env.empty sizefun_list in
     let env_of_sizefun_values =
       Env.map 
         (fun sizefun -> if l_rec then 
                           Global.Vsizefunrec(sizefun, f_to_exp_env)
                         else Global.Vsizefun(sizefun))
         f_to_exp_env in
     let l = Env.to_list env_of_sizefun_values in
     (* add a value for every global name *)
     let update_module_table d_names (name, m) =
       try
         let entry = Modules.find_value (Name name) in
         let value = Env.find m env_of_sizefun_values in
         Global.set_value_exp entry value;
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
  let { p_impl_list } as p, acc =
    if !Misc.nosizerec then p, empty
    else Mapfold.program_it funs empty p in
  (* remove empty declarations [let ()] *)
  let p_impl_list = List.filter Aux.not_empty_impl p_impl_list in
  (* flush specialized size function generated during the pass *)
  let sizefun_specialized_impl_list =
    flush_global_specialized_sizefun acc p_impl_list in
  { p with p_impl_list = sizefun_specialized_impl_list } 
