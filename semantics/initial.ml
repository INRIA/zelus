open Value
open Monad
open Opt

let boolean v =
  match v with
  | Vbool(b) -> return b | _ -> None

let integer v =
  match v with
  | Vint(i) -> return i | _ -> None

let basic v =
  match v with
  | Value(v) -> Some(v) | _ -> None
                             
let ifthenelse v v1 v2 =
  let+ v = boolean v in
  return (if v then v1 else v2)

let not_op v =
  let+ v = boolean v in
  return (Vbool(not v))

let uminus_op v =
  let+ v = integer v in
  return (Vint(- v))

let and_op v1 v2 =
  let+ v1 = boolean v1 in
  let+ v2 = boolean v2 in
  return (Vbool(v1 && v2))

let or_op v1 v2 =
  let+ v1 = boolean v1 in
  let+ v2 = boolean v2 in
  return (Vbool(v1 || v2))

let add_op v1 v2 =
  let+ v1 = integer v1 in
  let+ v2 = integer v2 in
  return (Vint(v1 + v2))

let minus_op v1 v2 =
  let+ v1 = integer v1 in
  let+ v2 = integer v2 in
  return (Vint(v1 - v2))
    
let mult_op v1 v2 =
  let+ v1 = integer v1 in
  let+ v2 = integer v2 in
  return (Vint(v1 * v2))

let div_op v1 v2 =
  let+ v1 = integer v1 in
  let+ v2 = integer v2 in
  return (Vint(v1 / v2))

let geti i v =
  let rec geti i v_list =
    match v_list with
    | [] -> None
    | v :: v_list -> if i = 0 then Some(v) else geti (i-1) v_list in
  match v with
  | Vtuple(v_list) -> if i >= 0 then geti i v_list else None
  | _ ->  None
  
(* The initial environment *)
