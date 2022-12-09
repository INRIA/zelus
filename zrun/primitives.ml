(* *********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
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

let (and+) v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(v1, v2)

let bool v =
  match v with
  | Vbool(b) -> return b
  | _ -> None

let int v =
  match v with
  | Vint(i) -> return i | _ -> None

let float v =
  match v with
  | Vfloat(i) -> return i | _ -> None

let vfloat v =
  match v with
  | Value(Vfloat(i)) -> return i | _ -> None

let get_present v =
  match v with
  | Vpresent(v) -> return v
  | _ -> None

let test v =
  match v with
  | Vpresent _ -> return (Vbool(true)) | Vabsent -> return (Vbool(false))
  | _ -> None
     
let get_node v =
  match v with
  | Vclosure ({ c_funexp = { f_kind = Knode | Khybrid } } as c) -> return c
  | _ -> None
       
let get_record r =
  match r with
  | Vrecord(l) -> return l
  | _ -> None
       
let ifthenelse_op v v1 v2 =
  let* b = bool v in
  if b then return v1 else return v2

let not_op v =
  let* v = bool v in
  return (Vbool(not v))

let uminus_op v =
  let* v = int v in
  return (Vint(- v))

let and_op v1 v2 =
  let* v1 = bool v1 in
  let* v2 = bool v2 in
  return (Vbool(v1 && v2))

let or_op v1 v2 =
  let* v1 = bool v1 in
  let* v2 = bool v2 in
  return (Vbool(v1 || v2))

let on_op v1 v2 = or_op v1 v2

let add_op v1 v2 =
  let* v1 = int v1 in
  let* v2 = int v2 in
  return (Vint(v1 + v2))

let minus_op v1 v2 =
  let* v1 = int v1 in
  let* v2 = int v2 in
  return (Vint(v1 - v2))
    
let mult_op v1 v2 =
  let* v1 = int v1 in
  let* v2 = int v2 in
  return (Vint(v1 * v2))

let div_op v1 v2 =
  let* v1 = int v1 in
  let* v2 = int v2 in
  return (Vint(v1 / v2))

let add_float_op v1 v2 =
  let* v1 = float v1 in
  let* v2 = float v2 in
  return (Vfloat(v1 +. v2))

let uminus_float_op v =
  let* v = float v in
  return (Vfloat(-. v))
  
let minus_float_op v1 v2 =
  let* v1 = float v1 in
  let* v2 = float v2 in
  return (Vfloat(v1 -. v2))
    
let mult_float_op v1 v2 =
  let* v1 = float v1 in
  let* v2 = float v2 in
  return (Vfloat(v1 *. v2))

let div_float_op v1 v2 =
  let* v1 = float v1 in
  let* v2 = float v2 in
  return (Vfloat(v1 /. v2))

let sqrt_op v =
  let* v = float v in
  return (Vfloat(sqrt v))

let mod_op v1 v2 =
  let* v1 = int v1 in
  let* v2 = int v2 in
  return (Vint(v1 mod v2))

let eq_op v1 v2 =
  return (Vbool(v1 = v2))

let lt_op v1 v2 =
  return (Vbool(v1 < v2))

let gt_op v1 v2 =
  return (Vbool(v1 > v2))

let lte_op v1 v2 =
  return (Vbool(v1 <= v2))

let gte_op v1 v2 =
  return (Vbool(v1 >= v2))

let length_op v =
  match v with
  | Varray(a) -> return (Vint(Array.length a))
  | _ -> none
       
let geti v i =
  let n = Array.length v in
  if (i < n) && (i >= 0) then return (Value(v.(i))) else None


(* ifthenelse. this one is strict w.r.t all arguments *)
let lustre_ifthenelse v1 v2 v3 =
  let+ v1 = v1 in
  let+ _ = v2 in
  let+ _ = v3 in
  ifthenelse_op v1 v2 v3

(* ifthenelse. this one is strict w.r.t the first argument *)
let lazy_ifthenelse v1 v2 v3 =
  let+ v1 = v1 in
  ifthenelse_op v1 v2 v3

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
(* an alternative semantics to the constructive semantics of Esterel *)
(* it is closer to the "logical semantics of Esterel" than the *)
(* the "constructive semantics" through it is not entirely clear. *)
(* note that this is very different than the treatment of activation *)
(* conditions (e.g., if c then eq1 else eq2 which correspond to a *)
(* condition on a clock. In that case, when c = bot, then the resulting *)
(* environment is also bot *)
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
  
let ifthenelse =
  if !Smisc.set_lustre then lustre_ifthenelse else
    if !Smisc.set_esterel then esterel_ifthenelse
    else lazy_ifthenelse

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

let constr1 f v_list =
  let+ v_list = slist v_list in
  return (Value(Vconstr1(f, v_list)))

let state1 f v_list =
  let+ v_list = slist v_list in
  return (Value(Vstate1(f, v_list)))

let array v_list =
  let+ v_list = slist v_list in
  return (Value(Varray(Array.of_list v_list)))

let lift f v =
  match v with | Vbot -> Vbot | Vnil -> Vnil | Value(v) -> Value(f v)
                                                         
(* if one component contains bot or nil, returns bot or nil *)
(*
let aatomic v =
  let (let+) x f =
  match x with | Vbot -> Vbot | Vnil -> Vnil | Value(v) -> f v in

  let rec slist v_list =
  match v_list with
  | [] -> Value []
  | v :: v_list ->
     let v_r = slist v_list in
     sapp (fun x xs -> x :: xs) v v_r in
  let+ v = v in
  match v with
  | Vtuple(v_list) ->
     let+ v_list = slist v_list in Value(Vstuple(v_list))
  | _ -> Value(v)
 *)

let atomic v =
  let+ v = v in
  match v with
  | Vtuple(l) -> stuple l
  | _ -> return (Value(v))
       
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
  let* v = int v in
  return (Vint(Random.int v))
let random_float_op v =
  let* v = float v in
  return (Vfloat(Random.float v))
    

(* The initial Stdlib *)
let list_of_primitives =
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

let list_of_random_primitives =
  ["random_bool", zerop random_bool_op;
   "random_int", unop random_int_op;
   "random_float", unop random_float_op]

let to_env acc l = List.fold_left (fun acc (n, v) -> Genv.E.add n v acc) acc l

let list_of_esterel_primitives =
  if !Smisc.set_esterel
  then ["or", esterel_or_op;
        "&", esterel_and_op]
  else []
  
let stdlib_env =
  { Genv.name = "Stdlib";
    Genv.values =
      to_env (to_env Genv.E.empty list_of_primitives) list_of_random_primitives }
    
    
