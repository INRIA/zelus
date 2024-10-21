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

(* values for arrays *)
open Misc
open Error
open Monad
open Result
open Value

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

(* Array operations - slice, concat, etc. *)
(* array operations *)
let concat loc v1 v2 =
  let concat v1 v2 =
    match v1, v2 with
    | Vflat(v1), Vflat(v2) ->
       return (Value(Varray(Vflat(Array.append v1 v2))))
    | Vmap { m_length = l1; m_u = mu1}, Vmap { m_length = l2; m_u = mu2 } ->
       let m_length = l1 + l2 in
       let m_u i = if i <= l1 then mu1 i else mu2 (i - l1) in
       return (Value(Varray(Vmap { m_length; m_u })))
    | Vmap { m_length; m_u }, Vflat(v) ->
       let m_u i = if i <= m_length
                   then m_u i else return (v.(i - m_length)) in
       let m_length = m_length + Array.length v in
       return (Value(Varray(Vmap { m_length; m_u })))
    | Vflat(v), Vmap { m_length; m_u } ->
       let lv = Array.length v in
       let m_length = m_length + lv in
       let m_u i = if i <= lv then return (v.(i)) else m_u (i - lv) in
       return (Value(Varray(Vmap { m_length; m_u }))) in
  let+ v1 = v1 and+ v2 = v2 in
  match v1, v2 with
  | Varray(v1), Varray(v2) ->
     concat v1 v2
  | _ -> error { kind = Etype; loc }

let get_in_array loc a i =
  match a with
  | Vflat(a) ->
     let n = Array.length a in
     if (i >= 0) && (i < n) then return (a.(i))
     else error { kind = Earray_size { size = n; index = i }; loc }
  | Vmap { m_length; m_u } ->
     if (i >= 0) && (i < m_length) then m_u i
     else error { kind = Earray_size { size = m_length; index = i }; loc }

let geti loc v i =
  match v with
  | Varray(a) ->
     get_in_array loc a i
  | _ -> error { kind = Etype; loc }

let get loc v i =
  let+ v = v and+ i = i in
  match v, i with
  | Varray(a), Vint(i) ->
     let* v = get_in_array loc a i in
     return (Value(v))
  | _ -> error { kind = Etype; loc }

let get_with_default loc v i default =
  let get a i =
    match a with
    | Vflat(a) ->
       let n = Array.length a in
       if (i >= 0) && (i < n) then return (Value(a.(i)))
       else return default
    | Vmap { m_length; m_u } ->
       if (i >= 0) && (i < m_length) then
         let* v = m_u i in return (Value(v))
       else return default in
  let+ v = v and+ i = i in
  match v, i with
  | Varray(a), Vint(i) -> get a i
  | _ -> error { kind = Etype; loc }

let slice loc v i1 i2 =
  let slice v i1 i2 = match v with
    | Vflat(a) ->
       let n = Array.length a in
       if i1 < n then
         if i2 < n then
           return (Value(Varray(Vflat(Array.sub a i1 (i2 - i1 + 1)))))
         else error { kind = Earray_size { size = n; index = i2 }; loc }
       else error { kind = Earray_size { size = n; index = i1 }; loc }
    | Vmap { m_length; m_u } ->
       if i1 < m_length then
         if i2 < m_length then
           return (Value(Varray(Vmap { m_length = i2 - i1 + 1; m_u })))
         else
           error { kind = Earray_size { size = m_length; index = i2 }; loc }
       else error { kind = Earray_size { size = m_length; index = i1 }; loc } in
  let+ v = v and+ i1 = i1 and+ i2 = i2 in
  match v, i1, i2 with
  | Varray(v), Vint(i1), Vint(i2) -> slice v i1 i2
  | _ -> error { kind = Etype; loc }

(* [| v with i <- w |] *)
let update loc v i w =
  let update v i w =
    match v with
    | Vflat(a) ->
       if (i >= 0) && (i < Array.length a) then
         let a = Array.copy a in
         a.(i) <- w;
         return (Vflat(a)) else return v
    | Vmap { m_length; m_u } ->
       return
         (Vmap { m_length; m_u = fun j -> if i = j then return w else m_u j }) in
  let+ a = v and+ i = i and+ w = w in
  match a, i with
  | Varray(a), Vint(i) ->
     let* a = update a i w in
     return (Value(Varray(a)))
  | _ -> error { kind = Etype; loc }

(* [| v with i1,..., in <- w |] is a shortcut for *)
(* [| v with i1 <- [| v.(i1) with i2,...,in <- w |] |] *)
let rec update_list loc v i_list w =
  match i_list with
  | [] -> error { kind = unexpected_failure; loc }
  | i :: i_list ->
     let* w = match i_list with
       | [] -> return w
       | _ -> let* v = get loc v i in
              update_list loc v i_list w in
     update loc v i w

(* conversion between a flat array and a map *)
let map_of_flat v =
  match v with
  | Vflat(f) ->
     return { m_length = Array.length f; m_u = fun i -> return (f.(i)) }
  | Vmap(v) -> return v
let flat_of_map v =
  let fill length a m_u =
    let rec fillrec length =
      if length = 0 then return a
      else let* v = m_u length in a.(length) <- v; fillrec (length - 1) in
    fillrec length in
  match v with
    | Vflat(f) -> return f
    | Vmap { m_length; m_u } ->
       if m_length = 0 then return ([||])
       else let* v = m_u 0 in
            let a = Array.make m_length v in
            let* v = fill m_length a m_u in
            return (v)

let dim loc v =
  match v with
  | Varray v ->
     let v = match v with
       | Vflat(a) -> Array.length a
       | Vmap { m_length } -> m_length in
     return v
  | _ -> error { kind = Etype; loc }

let dim_dim loc v =
  match v with
  | Varray(v) ->
     let r = match v with
       | Vflat(a) ->
          let* m = dim loc (a.(0)) in
          return (Array.length a, m)
       | Vmap { m_length; m_u } ->
          let* v = m_u 0 in
          let* m = dim loc v in
          return (m_length, m) in
     r
  | _ -> error { kind = Etype; loc }

(* [v i j] *)
let get_get loc v i j =
  let* v = geti loc v i in
  geti loc v j

(* transpose: input: ['n]['m]t. output: ['m]['n]t such that *)
(* output.(j).(i) = input.(i).(j) [i < 'n, j < 'm] *)
let transpose loc v =
  let+ v = v in
  let* n_i, m_j = dim_dim loc v in
  return
    (Value
       (Varray
          (Vmap
             { m_length = m_j;
               m_u = fun j ->
                     return (Varray(Vmap { m_length = n_i;
                                           m_u = fun i -> get_get loc v i j }))
    })))

(* flatten: imposes that the size of internal arrays are the same, that is *)
(* flatten : 'n,'m. ['n]['m]'a -> ['n * 'm]'a *)
(* flatten [|[| x_11; ...; x_1m |];...; [|x_n1;...;x_nm|]|] =
                             x_11; ...; x_1m; x_21;...; x_n1;...;x_nm *)
let flatten loc v =
  let+ v = v in
  let* n_i, m_j = dim_dim loc v in
  return
    (Value(Varray (Vmap { m_length = n_i * m_j;
                          m_u = fun i -> let q = i / m_j in
                                         let r = i mod m_j in
                                         get_get loc v q r })))

(* reverse *)
(* reverse [|x0;...;x_{n-1}|] = [|x_{n-1};...;x_0|] *)
let reverse loc v =
  let+ v = v in
  let* n = dim loc v in
  return 
    (Value(Varray(Vmap { m_length = n; m_u = fun i -> geti loc v (n-1-i) })))


