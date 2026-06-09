(***********************************************************************)
(*                                                                     *)
(*                        The ZRun Interpreter                         *)
(*                                                                     *)
(*                             Marc Pouzet                             *)
(*                                                                     *)
(*  (c) 2020-2026 Inria Paris                                          *)
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

(* type error for arrays *)
let typ_error_array = Etype(Some(Etyp_array))

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
let empty = Varray(Vflat([||]))

let is_array loc v =
  match v with
  | Varray(a) -> return a
  | _ -> error { kind = typ_error_array; loc }

let is_int loc i =
  match i with
  | Vint(i) -> return i | _ -> error { kind = Etype(Some(Etyp_int)); loc }

(* size/dimension of an array *)
let size a =
  match a with
  | Vflat(a) -> Array.length a
  | Vmap { m_length } -> m_length

let get_in_array loc a i =
  match a with
  | Vflat(a) ->
     let n = Array.length a in
     if (i >= 0) && (i < n) then return (a.(i))
     else error { kind = Earray_index { size = n; index = i }; loc }
  | Vmap { m_length; m_u } ->
     if (i >= 0) && (i < m_length) then m_u i
     else error { kind = Earray_index { size = m_length; index = i }; loc }

(* dimension of a value that must be an array *)
let dim loc v =
  let* v = is_array loc v in
  return (size v)

(* dimension of a matrix *)
(* fails if outer dimension is 0 *)
let dim_dim loc v =
  let* v = is_array loc v in
  let* v0 = get_in_array loc v 0 in
  let* v0 = is_array loc v0 in
  return (size v, size v0)

(* concat two arrays [v1] and [v2] *)
let concat loc v1 v2 =
  let concat v1 v2 =
    match v1, v2 with
    | Vflat(v1), Vflat(v2) ->
       return (Value(Varray(Vflat(Array.append v1 v2))))
    | Vmap { m_length = l1; m_u = mu1}, Vmap { m_length = l2; m_u = mu2 } ->
       let m_length = l1 + l2 in
       let m_u i = if i < l1 then mu1 i else mu2 (i - l1) in
       return (Value(Varray(Vmap { m_length; m_u })))
    | Vmap { m_length; m_u }, Vflat(v) ->
       let m_u i = if i < m_length
                   then m_u i else return (v.(i - m_length)) in
       let m_length = m_length + Array.length v in
       return (Value(Varray(Vmap { m_length; m_u })))
    | Vflat(v), Vmap { m_length; m_u } ->
       let lv = Array.length v in
       let m_length = m_length + lv in
       let m_u i = if i < lv then return (v.(i)) else m_u (i - lv) in
       return (Value(Varray(Vmap { m_length; m_u }))) in
  let+ v1 = v1 and+ v2 = v2 in
  match v1, v2 with
  | Varray(v1), Varray(v2) ->
     concat v1 v2
  | _ -> error { kind = Etype(Some(Etyp_array)); loc }

let geti loc v i =
  match v with
  | Varray(a) ->
     get_in_array loc a i
  | _ -> error { kind = Etype(Some(Etyp_array)); loc }

let get loc v i =
  let+ v = v and+ i = i in
  match v, i with
  | Varray(a), Vint(i) ->
     let* v = get_in_array loc a i in
     return (Value(v))
  | _ -> error { kind = Etype(Some(Etyp_array)); loc }

(* extend an array with an element at the end *)
let extend loc vi v =
  let i = size v in
  Vmap { m_length = i + 1;
         m_u = fun j -> if j = i then return vi else get_in_array loc v j }

let get_with_default loc v i default =
  let+ v = v and+ i = i in
  match v, i with
  | Varray(a), Vint(i) ->
      (match get_in_array loc a i with
      | Ok(vi) -> return (Value(vi))
      | _ -> return default)
  | _ -> error { kind = Etype(Some(Etyp_array)); loc }

(* [x.(i1 .. i2)] returns a slices of [x] between index [i1] and [i2] *)
(* if [x: [n]a] then [x.(i1 .. i2) : [i2-i1+1]a] *)
(* if [0 > i1] or [i1 > i2+1] or [i2+1 > n], the function fails *)
let slice loc v i1 i2 =
  let a = i1 in
  let b = i2 + 1 in
  let n = size v in
  if (0 <= a) && (a <= b) && (b <= n) then
    let ret = match v with
      | Vflat(arr) ->
        Vflat(Array.sub arr a (b - a))
      | Vmap { m_length = _; m_u } ->
        Vmap { m_length = (b - a); m_u = (fun i -> m_u (i + i1)) }
    in return (Value(Varray(ret)))
  else error { kind = Earray_slice { size = n; i1 = i1; i2 = i2 }; loc }

let slice_both loc v i1 i2 =
  let+ v = v and+ i1 = i1 and+ i2 = i2 in
  match v, i1, i2 with
  | Varray(v), Vint(i1), Vint(i2) -> slice loc v i1 i2
  | _ -> error { kind = Etype(Some(Etyp_array)); loc }

(* x.(e1..) *)
let slice_left loc v i1 =
  let+ v = v in
  let+ i1 = i1 in
  let* i1 = is_int loc i1 in
  let* a = is_array loc v in
  let l = size a in
  slice loc a i1 (l-1)

(* x.(..e2) *)
let slice_right loc v i2 =
  let+ v = v in
  let+ i2 = i2 in
  let* i2 = is_int loc i2 in
  let* a = is_array loc v in
  slice loc a 0 i2

(* [| v with i <- vi |] *)
(* returns v if i is out-of-bounds *)
let update loc v i vi =
  let+ v = v and+ i = i and+ vi = vi in
  match v, i with
  | Varray(v), Vint(i) ->
    let ret =
      if (0 <= i) && (i < size v) then
        match v with
          | Vflat(v) ->
            let v = Array.copy v in
            v.(i) <- vi;
            Vflat(v)
          | Vmap { m_length; m_u } ->
            Vmap { m_length; m_u = fun j -> if i = j then return vi else m_u j }
      else v
    in return (Value(Varray(ret)))
  | _ -> error { kind = Etype(Some(Etyp_array)); loc }

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
  match v with
  | Vflat(f) -> return f
  | Vmap { m_length; m_u } ->
      let l = List.init m_length m_u in
      let rec sift l = match l with
      | [] -> return []
      | x :: s -> let* x = x in let* s = sift s in return (x :: s)
      in let* l = sift l in
      return (Array.of_list l)

(* [v i j] *)
let get_get loc v i j =
  let* v = geti loc v i in
  geti loc v j

(* transpose: input: ['n]['m]t. output: ['m]['n]t such that *)
(* output.(j).(i) = input.(i).(j) [i < 'n, j < 'm] *)
(* fails if outer dimension in 0 *)
let transpose loc v =
  let+ v = v in
  let* n, m = dim_dim loc v in
  let outer j =
    let inner i = get_get loc v i j in
    return (Varray(Vmap { m_length = n; m_u = inner }))
  in return (Value (Varray (Vmap { m_length = m; m_u = outer })))

(* flatten: assumes that the size of internal arrays are the same, that is *)
(* flatten : 'n,'m. ['n]['m]'a -> ['n * 'm]'a *)
(* flatten [|[| x_11; ...; x_1m |];...; [|x_n1;...;x_nm|]|] =
                             x_11; ...; x_1m; x_21;...; x_n1;...;x_nm *)
(* fails if outer dimension in 0 *)
let flatten loc v =
  let+ v = v in
  let* n, m = dim_dim loc v in
  let m_u k =
    let i = k / m in
    let j = k mod m in
    get_get loc v i j
  in return (Value(Varray (Vmap { m_length = n * m; m_u })))

(* reverse *)
(* reverse [|x0;...;x_{n-1}|] = [|x_{n-1};...;x_0|] *)
let reverse loc v =
  let+ v = v in
  let* n = dim loc v in
  let m_u k = geti loc v (n-1-k) in
  return (Value(Varray(Vmap { m_length = n; m_u })))
