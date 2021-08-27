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
(* [let** x = e1 in e2] returns bot if v = bot; nil if v = nil; *)
(* e2[value(e1)/x] otherwise *)
let (let**) v f =
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) -> f v

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

let get_present v =
  match v with
  | Vpresent(v) -> return v
  | _ -> None

let test v =
  match v with
  | Vpresent _ -> return (Vbool(true)) | Vabsent -> return (Vbool(false))
  | _ -> None
 
let get_fun v =
  match v with
  | Vfun _ -> return v
  | _ -> None

let get_node v =
  match v with
  | Vnode v -> return v
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
  
let geti i v =
  let rec geti i v_list =
    match v_list with
    | [] -> None
    | v :: v_list -> if i = 0 then Some(v) else geti (i-1) v_list in
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) ->
     match v with
     | Vtuple(v_list) -> if i >= 0 then geti i v_list else None
     | _ -> None
          
(* ifthenelse *)
let ifthenelse v1 v2 v3 =
  match v1, v2, v3 with
  | Vbot, _, _ -> return Vbot
  | (Vnil, Vbot, _) | (Vnil, _, Vbot) -> return Vbot
  | Vnil, _, _ -> return Vnil
  | (Value(v1), _, _)  -> ifthenelse_op v1 v2 v3
                 
(* lift a unary operator: [op bot = bot]; [op nil = nil] *)
let lift1 op v =
  let** v = v in
  let* v = op v in
  return (Value v)

(* lift a binary operator: [op bot _ = bot]; [op _ bot = bot]; same for nil *)
let lift2 op v1 v2 =
  let v =
    match v1, v2 with
    | (Vbot, _) | (_, Vbot) -> Vbot
    | (Vnil, _) | (_, Vnil) -> Vnil
    | Value(v1), Value(v2) -> Value(op v1 v2) in
  return v

let sapp2 op v1 v2 =
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> Vbot
  | (Vnil, _) | (_, Vnil) -> Vnil
  | Value(v1), Value(v2) -> Value(op v1 v2)

(* convert a value into a list *)
let list_of v =
  match v with
  | Value(Vvoid) -> return []
  | Value(Vtuple(v_list)) -> return v_list
  | Value(Vstuple(v_list)) ->
     return (List.map (fun v -> Value(v)) v_list)
  | Vbot | Vnil | Value _ -> return [v]
              
(* gets the value *)
let pvalue v =
  match v with
  | Vnil | Vbot -> None
  | Value(v) -> return v

let is_pvalue v = not (is_none (pvalue v))
                    
(* builds a synchronous pair. If one is bot, the result is bot; *)
(* if one is nil, the result is nil *)
let spair v1 v2 =
  sapp2 (fun x1 x2 -> Vstuple [x1; x2]) v1 v2

(* if one is bot, return bot; if one is nil, return nil *)
let rec slist v_list =
  match v_list with
  | [] -> Value []
  | v :: v_list ->
     let v_r = slist v_list in
     sapp2 (fun x xs -> x :: xs) v v_r
     
let stuple v_list =
  let** v_list = slist v_list in
  return (Value(Vstuple(v_list)))
  
let constr1 f v_list =
  let** v_list = slist v_list in
  return (Value(Vconstr1(f, v_list)))

let atomic v =
  let** v = v in
  match v with
  | Vtuple(l) -> stuple l
  | _ -> return (Value(v))
       
(* void *)
let void = Value(Vvoid)

(* max float *)
let max_float = Value(Vfloat(max_float))

let zerop op = Vfun (fun _ -> op ())

let unop op = Vfun op

let binop op =
  Vfun(fun v1 -> return (Vfun (fun v2 -> op v1 v2)))
    
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
   ">=", binop gte_op]

let list_of_random_primitives =
  ["random_bool", zerop random_bool_op;
   "random_int", unop random_int_op;
   "random_float", unop random_float_op]

let to_env acc l = List.fold_left (fun acc (n, v) -> Genv.E.add n v acc) acc l
                 
let stdlib_env =
  { Genv.name = "Stdlib";
    Genv.values =
      to_env (to_env Genv.E.empty list_of_primitives) list_of_random_primitives }
    
    
