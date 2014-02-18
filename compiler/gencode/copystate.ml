(**************************************************************************)
(*                                                                        *)
(*  The Zelus Hybrid Synchronous Language                                 *)
(*  Copyright (C) 2012-2013                                               *)
(*                                                                        *)
(*  Timothy Bourke                                                        *)
(*  Marc Pouzet                                                           *)
(*                                                                        *)
(*  Universite Pierre et Marie Curie - Ecole normale superieure - INRIA   *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)
(* Stub code for passing/reading continuous states *)

open Misc
open Deftypes
open Obc
open Format



let void = make (Oconst Ovoid)
let wildpat = make (Owildpat)
let tuple l = make (Otuple(l))
let tuplepat l = make (Otuplepat(l))
let app op l = make (Oapp(op, l))
let local n = make (Olocal(n, Obc.Val))
let global n = make (Oglobal(n))
let varpat n = make (Ovarpat(n))

let solver_fn n = Lident.Modname { Lident.qual = "ZLS"; Lident.id = n }

(** create accessor and mutator functions for, respectively, *)
(** array_to_structure and assign_from_vars. *)

let make_get get_fn array_ident idx =
  Oapp (get_fn, [make (Olocal (array_ident, Val)); idx])

let make_set set_fn array_ident idx var =
  Oapp (set_fn, [make (Olocal (array_ident, Val)); idx; var])

(** copy an array into a tuple structure. This is done according to the *)
(** type structure *)
let array_to_structure get typ =
  let rec copy n ty =
    match ty.t_desc with
    | Tconstr(l, _, _) when l = Initial.unit_ident ->
        (n, Oconst Ovoid)
    | Tconstr(l, _, _) when l = Initial.float_ident ->
        (n + 1, get (make (Oconst (Oint n))))
    | Tconstr(l, _, _) when l = Initial.bool_ident ->
        (n + 1, get (make (Oconst (Oint n))))
    | Tproduct(ty_list) ->
        let (n, ty_list) = List.fold_left copy_list (n, []) ty_list in
        (n, Otuple (List.rev ty_list))
    | Tlink(ty) -> copy n ty
    | _ -> assert false
  and copy_list (n, rs) ty = let (n, r) = copy n ty in (n, make r :: rs) in
  make (snd (copy 0 typ))

(** generate a complete pattern where components with basic types are *)
(** variables. E.g., [(x1,(x2,x3),(x4, x5, x6)) if the x_i are of type bool/float *)
let flatten_typ_pattern prefix typ =
  let rev_vars (n, vars, r) = (List.rev vars, r) in
  let rec flatten n vars ty =
    match ty.t_desc with
    | Tconstr(l, _, _) when l = Initial.float_ident ->
        let v = Ident.fresh prefix in
        (n + 1, v :: vars, varpat v)
    | Tconstr(l, _, _) when l = Initial.bool_ident ->
        let v = Ident.fresh prefix in
        (n + 1, v::vars, varpat v)
    | Tproduct(ty_list) ->
        let (n, vars, r_list) = 
          List.fold_left 
            (fun (n, vars, rs) ty -> let n, vars, r = flatten n vars ty in
                                     n, vars, r :: rs)
            (n, vars, []) ty_list in
        (n, vars, make (Otuplepat (List.rev r_list)))
    | Tlink(ty) -> flatten n vars ty
    | _ -> (n, vars, make (Owildpat)) in
  rev_vars (flatten 0 [] typ)

(** Generate a sequence of calls to copy a structure into an array *)
(** set 1 x_1; ...; set n x_n *)
let assign_from_vars set vars after =
  let assign (n, r) v =
    let idx = make (Oconst (Oint n)) in
    let var = make (Olocal (v, Val)) in
    let assign = set idx var in
    (n + 1, make (Osequence (make assign, r))) in
  snd (List.fold_left assign (0, after) vars)

(* Generation of stub code for translating a tuple state into an array state *)
(* and conversely *)
(* Let [f: z_type * lx_type * bool * unit -> upz_type * dx_type * unit] *)
(* This generates a code of the form *)
(* [f t_lx_type t_z_type t_dx_type t_upz_typ bool] with *)
(* [lx_type = tuple_of_array t_lx_type] ... [t_dx_type = array_of_tuple dx_type] *)

let main ff qualid =
  let add_step_suffix qid = { qid with Lident.id = qid.Lident.id ^ "_step" } in

  let (ty_z, ty_lastx), (ty_upz, ty_dx) = 
    match !hybrid_mode with
    | DeltadelayTuple  -> 
        Ode.concrete_type Location.no_location (Lident.Modname(qualid))
    | _ -> 
        eprintf "The requested hybrid translation is not yet implemented.";
        raise Error
     in

  (* arrays in which states are stored *)
  let array_z  = Ident.fresh "z" in
  let array_lastx  = Ident.fresh "lastx" in
  let array_upz = Ident.fresh "upz" in
  let array_dx = Ident.fresh "dx" in

  let get_z     = make_get (solver_fn "get_zc") array_z in
  let get_lastx = make_get (solver_fn "get_cs") array_lastx in
  let set_lastx = make_set (solver_fn "set_cs") array_lastx in
  let set_dx    = make_set (solver_fn "set_cs") array_dx in
  let set_upz   = make_set (solver_fn "set_zx") array_upz in

  let discrete = Ident.fresh "d" in
  let memory = Ident.fresh "memory" in

  let goagain = Ident.fresh "goagain" in

  let result = Ident.fresh "result" in
  let resultpat = tuplepat [varpat goagain; varpat result] in

  (* inputs and outputs for implementing periods with horizons *)
  let time = Ident.fresh "time" in
  let next_time = Ident.fresh "next_time" in
  let r, time_arg, result_pat =
    if !Misc.compile_periods_into_discrete_counters
    then tuple [local result; local goagain; local next_time],
         [local time],
         (* tuplepat [resultpat; varpat next_time] *)
         tuplepat [varpat goagain; tuplepat [varpat result; varpat next_time]]
    else tuple [local result; local goagain; global (Lident.Name("infinity"))],
         [],
         resultpat in
  let return_horizon e = make (Osequence (e, r)) in

  (* copy structures to arrays and conversely *)
  let z = array_to_structure get_z ty_z in
  let lastx = array_to_structure get_lastx ty_lastx in
  let upz_vars, upz_pat = flatten_typ_pattern "upz" ty_upz in
  let dx_vars, dx_pat = flatten_typ_pattern "dx" ty_dx in
  
  let lhs = tuplepat ([upz_pat; dx_pat; result_pat]) in
  let step = 
    app (Lident.Modname (add_step_suffix qualid))
      ([local memory; z; lastx; local discrete] @ time_arg @ [void]) in
  
  (* create a sequence of array assignments to dx: *)
  (*   array_dx[0] <- dx_0;... *)
  let copy_to_lastx = assign_from_vars set_lastx dx_vars void in
  let copy_to_dx = assign_from_vars set_dx dx_vars void in
  let blit_if = 
    make (Oifthenelse(local discrete, copy_to_lastx, copy_to_dx)) in
  let copy_to_upz = assign_from_vars set_upz upz_vars blit_if in
  let body = make (Olet ([(lhs, step)], return_horizon copy_to_upz)) in
  
  let makearg id = varpat id in
  let main = make
    (Oletfun
      ("main", 
       [tuplepat 
           (List.map makearg
             [array_lastx; array_dx; array_upz; array_z; discrete; time])
       ],
       body)) in
  let init = make (Oletvalue (Ident.name memory, app (Lident.Modname qualid) [])) in

  Modules.initialize "__Main";
  Oprinter.implementation_list ff false [init; main]

