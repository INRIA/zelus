open Value
open Monad
open Opt
open Lident
   
(* let (let++) e f =
  match e with
  | None -> None
  | Some(v) ->
     match v with
     | Vtuple _ -> None
     | Value(v) ->
        match v with
        | Vnil -> return Vnil
        | Vbot -> return Vbot
        | Val(v) -> f v *)


let boolean v =
  match v with
  | Vbool(b) -> return b
  | _ -> None

let integer v =
  match v with
  | Vint(i) -> return i | _ -> None

let basic v =
  match v with
  | Value(v) -> Some(v)
  | _ -> None

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

let print_lident ff lident =
  match lident with
  | Name(s) -> Format.fprintf ff "%s" s
  | Modname { qual; id } -> Format.fprintf ff "%s.%s" qual id
                              
let print_b ff v =
  match v with
  | Vint(i) -> Format.fprintf ff "%i" i
  | Vbool(b) -> Format.fprintf ff "%s" (if b then "true" else "false")
  | Vfloat(f) -> Format.fprintf ff "%f" f
  | Vchar(c) -> Format.fprintf ff "%c" c
  | Vstring(s) -> Format.fprintf ff "%s" s
  | Vvoid -> Format.fprintf ff "()"

let rec print ff v =
  match v with
  | Value(v) -> print_b ff v
  | Vtuple(l) ->
     Format.fprintf ff "@[(%a)@]" (print_list print) l
  | Vconstr0(lid) -> print_lident ff lid
  | Vbot -> Format.fprintf ff "bot"
  | Vnil -> Format.fprintf ff "nil"

and print_list print ff l =
  match l with
  | [] -> assert false
  | [x] -> print ff x
  | x :: l -> Format.printf "@[%a,@,%a@]" print x (print_list print) l

let print_list ff l = print_list print ff l
                        
(* The initial environment *)
