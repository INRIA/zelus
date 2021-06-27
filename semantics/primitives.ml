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

open Value
open Monad
open Opt
open Lident
   
module Genv = Map.Make(Lident)

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
  match v with
  | Vbot -> return Vbot
  | Vnil -> return Vnil
  | Value(v) ->
     let* v = op v in
     return (Value v)

(* lift a binary operator: [op bot _ = bot]; [op _ bot = bot]; same for nil *)
let lift2 op v1 v2 =
  match v1, v2 with
  | Vbot, _ -> return Vbot
  | _, Vbot -> return Vbot
  | Vnil, _ -> return Vnil
  | _, Vnil -> return Vnil
  | Value(v1), Value(v2) ->
     let* v = op v1 v2 in
     return (Value v)

(* pairs and tuples *)
let unbot v1 v2 = 
  match v1, v2 with
  | (Vbot, _) | (_, Vbot) -> None
  | _ -> Some (v1, v2)

let rec unbot_list v_list =
  match v_list with
  | [] -> return []
  | [v] -> let* v = match v with | Vbot -> None | _ -> Some([v]) in
           return v
  | v1 :: v2 :: v_list ->
     let* v_list = unbot_list v_list in
     match unbot v1 v2 with
     | None -> None
     | Some(v1, v2) -> return (v1 :: v2 :: v_list)

let unnil v1 v2 = 
  match v1, v2 with
  | (Vnil, _) | (_, Vnil) -> None
  | _ -> Some (v1, v2)
 
let rec unnil_list v_list =
  match v_list with
  | [] -> return []
  | [v] -> let* v = match v with | Vnil -> None | _ -> Some([v]) in
           return v
  | v1 :: v2 :: v_list ->
     let* v_list = unnil_list v_list in
     match unnil v1 v2 with
     | None -> None
     | Some(v1, v2) -> return (v1 :: v2 :: v_list)

(* builds a pair. If one is bot, the result is bot; if one is nil, *)
(* the result is nil *)
let strict_pair v1 v2 =
  let v = unbot v1 v2 in
  match v with
  | None -> Vbot
  | Some(v1, v2) ->
     let v = unnil v1 v2 in
     match v with
     | None -> Vnil
     | Some(v1, v2) -> Value(Vtuple [v1; v2])
                     
let strict_tuple v_list =
  let v = unbot_list v_list in
  match v with
  | None -> Vbot
  | Some(v_list) ->
     let v = unnil_list v_list in
     match v with
     | None -> Vnil
     | Some(v_list) -> Value(Vtuple(v_list))

let strict_constr1 f v_list =
  let v = unbot_list v_list in
  match v with
  | None -> Vbot
  | Some(v_list) ->
     let v = unnil_list v_list in
     match v with
     | None -> Vnil
     | Some(v_list) -> Value(Vconstr1(f, v_list))

let tuple v_list =
  match v_list with
  | [] -> None
  | [v] -> return v
  | _ -> return (Value(Vtuple(v_list)))
      

(* check that v is an empty list *)
let zero v =
  match v with
  | [] -> return ()
  | _ -> None

(* check that v is a list of length one *)
let one v =
  match v with
  | [v] -> return v
  | _ -> None

(* check that v is a list of length two *)
let two v =
  match v with
  | [v1;v2] -> return (v1, v2)
  | _ -> None
       
let zerop op =
  CoFun (fun v -> let* _ = zero v in let* v = op () in return [Value v])

let unop op =
  CoFun (fun v -> let* v = one v in let* v = lift1 op v in return [v])

let binop op =
  CoFun
    (fun v -> let* (v1, v2) = two v in let* v = lift2 op v1 v2 in return [v])

(* state processes *)
let unop_process op s =
  CoNode
    { init = s;
      step =
        fun s (_: value list) ->
        let* v = op s in
        return ([v], s) }

let binop_process op s =
  CoNode
    { init = s;
      step =
        fun s v ->
        let* v = one v in
        let* v = lift1 (op s) v in
        return ([v], s) }

(* The initial environment *)
let genv0 =
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

let genv0 =
  List.fold_left
    (fun acc (n, v) -> Genv.add (Name n) (Gfun v) acc) Genv.empty genv0
  
let _ = Random.init 0

let random_bool_op () = return (Vbool(Random.bool()))
let random_int_op v =
  let* v = int v in
  return (Vint(Random.int v))
let random_float_op v =
  let* v = float v in
  return (Vfloat(Random.float v))
    
let genv1 =
  ["random_bool", zerop random_bool_op;
   "random_int", unop random_int_op;
   "random_float", unop random_float_op]

let genv0 =
  List.fold_left
    (fun acc (n, v) -> Genv.add (Name n) (Gfun v) acc) genv0 genv1
