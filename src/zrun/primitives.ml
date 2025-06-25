(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2024 Inria Paris                                          *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique. All rights reserved. This file is distributed under   *)
(*  the terms of the INRIA Non-Commercial License Agreement (see the   *)
(*  LICENSE file).                                                     *)
(*                                                                     *)
(* *********************************************************************)

open Misc
open Value
open Monad
open Opt
open Lident

(* remove dot and nil. *)
(* [let+ x = e in e'] returns [bot] if [e] returns bot; *)
(* nil if e returns nil; [e'] otherwise *)
let (let+) v f =
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) -> f v

let (let-) v f =
  match v with
  | Vbot -> return Vbot
  | _ -> f v

let (and+) v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(v1, v2)

let is_bool v =
  match v with
  | Vbool(b) -> return b
  | _ -> None

let is_int v =
  match v with
  | Vint(i) -> return i | _ -> None

let is_float v =
  match v with
  | Vfloat(i) -> return i | _ -> None

let is_vfloat v =
  match v with
  | Value(Vfloat(i)) -> return i | _ -> None

let is_array v =
  match v with
  | Varray(v) -> return v | _ -> None

let is_present v =
  match v with
  | Vpresent(v) -> return v
  | _ -> None

let test v =
  match v with
  | Vpresent _ -> return (Vbool(true)) | Vabsent -> return (Vbool(false))
  | _ -> None

let get_node v =
  match v with
  | Vclosure ({ c_funexp = { f_kind = Knode _ } } as c) -> return c
  | _ -> None

let get_record r =
  match r with
  | Vrecord(l) -> return l
  | _ -> None

let ifthenelse_op v v1 v2 =
  let* b = is_bool v in
  if b then return v1 else return v2

let not_op v =
  let* v = is_bool v in
  return (Vbool(not v))

let uminus_op v =
  let* v = is_int v in
  return (Vint(- v))

let and_op v1 v2 =
  let* v1 = is_bool v1 in
  let* v2 = is_bool v2 in
  return (Vbool(v1 && v2))

let or_op v1 v2 =
  let* v1 = is_bool v1 in
  let* v2 = is_bool v2 in
  return (Vbool(v1 || v2))

let on_op v1 v2 = or_op v1 v2

let add_op v1 v2 =
  let* v1 = is_int v1 in
  let* v2 = is_int v2 in
  return (Vint(v1 + v2))

let minus_op v1 v2 =
  let* v1 = is_int v1 in
  let* v2 = is_int v2 in
  return (Vint(v1 - v2))

let mult_op v1 v2 =
  let* v1 = is_int v1 in
  let* v2 = is_int v2 in
  return (Vint(v1 * v2))

let div_op v1 v2 =
  let* v1 = is_int v1 in
  let* v2 = is_int v2 in
  return (Vint(v1 / v2))

let add_float_op v1 v2 =
  let* v1 = is_float v1 in
  let* v2 = is_float v2 in
  return (Vfloat(v1 +. v2))

let uminus_float_op v =
  let* v = is_float v in
  return (Vfloat(-. v))

let minus_float_op v1 v2 =
  let* v1 = is_float v1 in
  let* v2 = is_float v2 in
  return (Vfloat(v1 -. v2))

let mult_float_op v1 v2 =
  let* v1 = is_float v1 in
  let* v2 = is_float v2 in
  return (Vfloat(v1 *. v2))

let div_float_op v1 v2 =
  let* v1 = is_float v1 in
  let* v2 = is_float v2 in
  return (Vfloat(v1 /. v2))

let sqrt_op v =
  let* v = is_float v in
  return (Vfloat(sqrt v))

let sin_op v =
  let* v = is_float v in
  return (Vfloat(sin v))

let cos_op v =
  let* v = is_float v in
  return (Vfloat(cos v))

let abs_float_op v =
  let* v = is_float v in
  return (Vfloat(abs_float v))

let abs_op v =
  let* v = is_int v in
  return (Vint(abs v))

let mod_op v1 v2 =
  let* v1 = is_int v1 in
  let* v2 = is_int v2 in
  return (Vint(v1 mod v2))

let length v =
  match v with
  | Vmap { m_length } -> m_length | Vflat(a) -> Array.length a
let length_op v =
  match v with
  | Varray(a) -> return (Vint(length a))
  | _ -> none

let rec compare_list compare p_list1 p_list2 =
  match p_list1, p_list2 with
  | [], [] -> return 0
  | p1 :: p_list1, p2 :: p_list2 ->
     let* v = compare p1 p2 in
     if v = 0 then compare_list compare p_list1 p_list2 else return v
  | _ -> none
    
let stdlib_name id = { qual = name_of_stdlib_module; id }
let present_name = Lident.Modname(stdlib_name "P")
let absent_name = Lident.Modname(stdlib_name "A")

let rec compare_pvalue v1 v2 =
  match v1, v2 with
  | Vint i1, Vint i2 -> return (compare i1 i2)
  | Vbool b1, Vbool b2 -> return (compare b1 b2)
  | Vfloat f1, Vfloat f2 -> return (compare f1 f2)
  | Vchar c1, Vchar c2 -> return (compare c1 c2)
  | Vstring s1, Vstring s2 -> return (compare s1 s2)
  | Vvoid, Vvoid -> return 0
  | Vconstr0(id1), Vconstr0(id2) -> return (Lident.compare id1 id2)
  | Vconstr1(id1, p_list1), Vconstr1(id2, p_list2) ->
     let v = Lident.compare id1 id2 in
     if v = 0 then
       compare_list compare_pvalue p_list1 p_list2 else return v
  | Vpresent(v1), Vpresent(v2) -> compare_pvalue v1 v2
  | Vabsent, Vabsent -> return 0
  (* or one is the lower-level internal representation of the other *)
  | (Vpresent(v1), v2) | (v2, Vpresent(v1)) -> compare_present v1 v2
  | (Vabsent, v) | (v, Vabsent) when is_absent v -> return 0
  | Vstuple(p_list1), Vstuple(p_list2) -> 
     compare_list compare_pvalue p_list1 p_list2
  | Vstate0(id1), Vstate0(id2) -> return (Ident.compare id1 id2)
  | Vstate1(id1, p_list1), Vstate1(id2, p_list2) ->
     let v = Ident.compare id1 id2 in
     if v = 0 then compare_list compare_pvalue p_list1 p_list2 else return v
  | Varray(v1), Varray(v2) -> 
     if length v1 = length v2 then compare_array compare_pvalue v1 v2 else none
  | Vrecord _, Vrecord _ -> none
  | Vtuple(v_list1), Vtuple(v_list2) ->
     compare_list compare_value v_list1 v_list2
  | Vfun _, Vfun _ -> none
  | Vclosure _, Vclosure _ -> none
  | _ -> none

(* comparison of present/absent with one the representation of the other *)
and compare_present v1 v2 =
  match v2 with
  | Vconstr1(ln, [v2]) when ln = present_name -> compare_pvalue v1 v2
  | _ -> none

and is_absent v = 
  match v with 
  | Vconstr0(ln) when ln = absent_name -> true | _ -> false

and compare_array compare a1 a2 =
  (* compare the elements of two arrays, from left to right *)
  let compare_array_n n (get_a1, a1) (get_a2, a2) =
    let rec compare_array_n i n =
    if i < n then
      let* p1 = get_a1 a1 i in
      let* p2 = get_a2 a2 i in
      let* v = compare_pvalue p1 p2 in
      if v = 0 then compare_array_n (i+1) n else return v
    else return 0 in
    compare_array_n 0 n in
  let get_i_array a i = return (a.(i)) in
  let get_i a i = Result.to_option (a i) in
  let n = length a1 in
  match a1, a2 with
  | Vflat(a1), Vflat(a2) -> 
      compare_array_n n (get_i_array, a1) (get_i_array, a2)
  | Vflat(a1), Vmap({ m_u }) -> 
      compare_array_n n (get_i_array, a1) (get_i, m_u)
  | Vmap({ m_u }), Vflat(a2) -> 
      compare_array_n n (get_i, m_u) (get_i_array, a2)
  | Vmap({ m_u = a1 }), Vmap({ m_u = a2 }) -> 
    compare_array_n n (get_i, a1) (get_i, a2)

and compare_value v1 v2 =
  match v1, v2 with
  | (Vbot, Vbot) | (Vnil, Vnil) -> return 0
  | (Value(v1), Value(v2)) -> compare_pvalue v1 v2
  | _ -> none
                                
let eq_op v1 v2 =
  let* v = compare_pvalue v1 v2 in
  return (Vbool(v = 0))

let lt_op v1 v2 =
  let* v = compare_pvalue v1 v2 in
  return (Vbool(v = -1))

let gt_op v1 v2 =
  let* v = compare_pvalue v1 v2 in
  return (Vbool(v = 1))

let lte_op v1 v2 =
  let* v = compare_pvalue v1 v2 in
  return (Vbool(v <= 0))

let gte_op v1 v2 =
  let* v = compare_pvalue v1 v2 in
  return (Vbool(v >= 0))

       
(* ifthenelse. this one is strict w.r.t all arguments *)
let lustre_ifthenelse v1 v2 v3 =
  let+ v1 = v1 in
  let- v2 = v2 in
  let- v3 = v3 in
  ifthenelse_op v1 v2 v3

(* ifthenelse. this one is strict w.r.t the first argument *)
let lazy_ifthenelse v1 v2 v3 =
  let+ v1 = v1 in
  ifthenelse_op v1 v2 v3

(* the constructive semantics for the boolean operators [or] and [and] *)
let esterel_or_op v1 v2 =
  match v1, v2 with
  | (Value(Vbool(true)), (Vbot | Vnil)) | ((Vbot|Vnil), Value(Vbool(true)))
    | (Value(Vbool(true)), Value(Vbool _))
    | (Value(Vbool _), Value(Vbool(true))) -> return (Value(Vbool(true)))
  | (Value(Vbool(false)), Vbot) | (Vbot, Value(Vbool(false))) -> return Vbot
  | (Value(Vbool(false)), Vnil) | (Vnil, Value(Vbool(false))) -> return Vnil
  | (Value(Vbool(false)), Value(Vbool v)) -> return (Value(Vbool(v)))
  | (_, Vbot) | (Vbot, _) -> return Vbot
  | (_, Vnil) | (Vnil, _) -> return Vnil
  | _ -> none

let esterel_and_op v1 v2 =
  match v1, v2 with
  | (Value(Vbool(false)), (Vbot | Vnil)) | ((Vbot|Vnil), Value(Vbool(false)))
    | (Value(Vbool(false)), Value(Vbool _))
    | (Value(Vbool _), Value(Vbool(false))) -> return (Value(Vbool(false)))
  | (Value(Vbool(true)), Vbot) | (Vbot, Value(Vbool(true))) -> return Vbot
  | (Value(Vbool(true)), Vnil) | (Vnil, Value(Vbool(true))) -> return Vnil
  | (Value(Vbool(true)), Value(Vbool v)) -> return (Value(Vbool(v)))
  | (_, Vbot) | (Vbot, _) -> return Vbot
  | (_, Vnil) | (Vnil, _) -> return Vnil
  | _ -> none

(* this one is a bit experimental; it can be used to implement *)
(* the constructive semantics of Esterel but does not coincide exactly *)
(* with Esterel. It relies on the fact that we consider that a decidable *)
(* equality exists on instantaneous value. This is true for the Esterel *)
(* language --- all imported operations are supposed to terminate --- whereas *)
(* it is wrong in the general case. *)
(* It is an alternative semantics to the constructive semantics of Esterel *)
(* that accept more programs, in particular [x = if x then true else true] *)
(* is causal with this whereas it is not in the original semantics of Esterel *)
(* note that an activation condition [if c then eq1 else eq2] which *)
(* corresponds to a condition on a clock returns bot as soon as [c = bot] *)
let esterel_ifthenelse v1 v2 v3 =
  match v1 with
  | Value(v1) -> ifthenelse_op v1 v2 v3
  | _ -> return (if v2 = v3 then v2 else v1)

let esterel_ifthenelse v1 v2 v3 =
  if v2 = v3 then return v2
  else lazy_ifthenelse v1 v2 v3
(* with it, we can define [or_gate] and [and_gate] *)
(* with three values:
 *- or(x, true) = or(true, x) = true
 *- and(x, false) = and(false, x) = false
 *- with or(x, y) = if x then true else y
 *- with and(x, y) = if x then y else false

let or_gate(x,y) = if x then true else y
let and_gate(x,y) = if x then y else false
Hence, [x = x or true] == [x = if x then true else true = true]
*)
let ifthenelse v1 v2 v3 =
  if !lustre then lustre_ifthenelse v1 v2 v3 else
    if !esterel then esterel_ifthenelse v1 v2 v3
    else lazy_ifthenelse v1 v2 v3

(* lift a unary operator: [op bot = bot]; [op nil = nil] *)
let lift1 op v =
  let+ v = v in
  let* v = op v in
  return (Value v)

(* lift a binary operator: [op bot _ = bot]; [op _ bot = bot]; same for nil *)
let sapp op v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(op v1 v2)

let lift2 op v1 v2 = return (sapp op v1 v2)

(* convert a value into a list *)
let list_of v =
  match v with
  | Value(Vvoid) -> []
  | Value(Vtuple(v_list)) -> v_list
  | Value(Vstuple(v_list)) ->
     List.map (fun v -> Value(v)) v_list
  | Vbot | Vnil | Value _ -> [v]

(* gets the value *)
let pvalue v =
  match v with
  | Vnil | Vbot -> None
  | Value(v) -> return v

(* if one is bot, return bot; if one is nil, return nil *)
let rec slist v_list =
  match v_list with
  | [] -> Value []
  | v :: v_list ->
     let v_r = slist v_list in
     sapp (fun x xs -> x :: xs) v v_r

let stuple v_list =
  let+ v_list = slist v_list in
  return (Value(Vstuple(v_list)))

let srecord l_v_list =
  let+ l_v_list = slist l_v_list in
  return (Value(Vrecord(l_v_list)))

let constr1 f v_list =
  let+ v_list = slist v_list in
  return (Value(Vconstr1(f, v_list)))

let state1 f v_list =
  let+ v_list = slist v_list in
  return (Value(Vstate1(f, v_list)))

let array v_list =
  let+ v_list = slist v_list in
  return (Value(Varray(Vflat(Array.of_list v_list))))

let lift f v =
  match v with | Vbot -> Vbot | Vnil -> Vnil | Value(v) -> Value(f v)

let atomic v =
  let+ v = v in
  match v with
  | Vtuple(l) -> stuple l
  | Vclosure _ -> 
      (* this part should be changed into [atomic(f) = lambda x.let+ x in f x] *)
      (* that is, even if [f] is not strict, make it a strict function *)
      (* this is necessary to avoid unbounded recursion with f = \x. x x and f f *)
      (* this is because Zrun applies to untyped programs *)
    return (Value v)
  | _ -> return (Value v)

(* void *)
let void = Value(Vvoid)

(* max float *)
let max_float = Value(Vfloat(max_float))
let zero_float = Value(Vfloat(0.0))

let zerop op = Vfun (fun _ -> op ())

let unop op = Vfun op

let binop op =
  Vfun(fun v1 -> return (Vfun (fun v2 -> op v1 v2)))

(*
(* state processes *)
let zerop_process op s =
  Vnode
    { init = s;
      step =
        fun s _ -> let* v = op s in return (v, s)
    }

let unop_process op s =
  Vnode
    { init = s;
      step =
        fun s v -> let* v = lift1 (op s) v in return (v, s) }
 *)

let _ = Random.init 0

let random_bool_op _ =
  return (Vbool(Random.bool()))
let random_int_op v =
  let* v = is_int v in
  return (Vint(Random.int v))
let random_float_op v =
  let* v = is_float v in
  return (Vfloat(Random.float v))


(* The initial Stdlib *)
let list_of_primitives () =
  ["+", binop add_op;
   "-", binop minus_op;
   "~-", unop uminus_op;
   "-", binop minus_op;
   "/", binop div_op;
   "*", binop mult_op;
   "+.", binop add_float_op;
   "-.", binop minus_float_op;
   "~-.", unop uminus_float_op;
   "-.", binop minus_float_op;
   "/.", binop div_float_op;
   "*.", binop mult_float_op;
   "sqrt", unop sqrt_op;
   "sin", unop sin_op;
   "cos", unop cos_op;
   "abs_float", unop abs_float_op;
   "abs", unop abs_op;
   "not", unop not_op;
   "&&", binop and_op;
   "&", binop and_op;
   "or", binop or_op;
   "||", binop or_op;
   "mod", binop mod_op;
   "=", binop eq_op;
   "<", binop lt_op;
   ">", binop gt_op;
   "<=", binop lte_op;
   ">=", binop gte_op;
   "length", unop length_op]

let list_of_random_primitives () =
  ["random_bool", zerop random_bool_op;
   "random_int", unop random_int_op;
   "random_float", unop random_float_op]

let to_env acc l = List.fold_left (fun acc (n, v) -> Genv.E.add n v acc) acc l

let list_of_esterel_primitives =
  if !esterel then ["or", esterel_or_op; "&", esterel_and_op] else []

let stdlib_env () =
  { Genv.name = "Stdlib";
    Genv.values =
      to_env (to_env Genv.E.empty (list_of_primitives ()))
        (list_of_random_primitives ()) }

