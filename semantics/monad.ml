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

module Opt =
  struct
    (* [let* x = e in f x] *)
    let (let*) e f =
      match e with
      | None -> None
      | Some(v) -> f v
                 
    let (and*) v1 v2 =
      match v1, v2 with
      | None, _ | _, None -> None
      | Some(v1), Some(v2) -> Some(v1, v2)
                              
    let return v = Some(v)

    let rec map f x_list =
      match x_list with
      | [] -> return []
      | x :: x_list ->
         let* xv = f x in
         let* x_list = map f x_list in
         return (xv :: x_list)

    let rec fold f acc x_list =
      match x_list with
      | [] -> return acc
      | x :: x_list ->
         let* acc = f acc x in
         fold f acc x_list

    let rec seqfold f acc x_seq =
      match x_seq () with
      | Seq.Nil -> return acc
      | Seq.Cons(x, x_seq) ->
         let* acc = f acc x in
         seqfold f acc x_seq

    let rec fold2 f acc x_list y_list =
      match x_list, y_list with
      | [], [] -> return acc
      | x :: x_list, y :: y_list ->
         let* acc = f acc x y in
         let* acc = fold2 f acc x_list y_list in
         return acc
      | _ -> None

    let rec map2 f x_list y_list =
      match x_list, y_list with
      | [], [] -> return []
      | x :: x_list, y :: y_list ->
         let* z = f x y in
         let* z_list = map2 f x_list y_list in
         return (z :: z_list)
      | _ -> None

    let rec map3 f x_list y_list z_list =
      match x_list, y_list, z_list with
      | [], [], [] -> return []
      | x :: x_list, y :: y_list, z :: z_list ->
         let* t = f x y z in
         let* t_list = map3 f x_list y_list z_list in
         return (t :: t_list)
      | _ -> None

    let rec mapfold f acc x_list =
      match x_list with
      | [] -> return (acc, [])
      | x :: x_list ->
         let* acc, s = f acc x in
         let* acc, s_list = mapfold f acc x_list in
         return (acc, s :: s_list)

    let rec mapfold2 f acc x_list y_list =
      match x_list, y_list with
      | [], [] -> return (acc, [])
      | x :: x_list, y :: y_list ->
         let* acc, s = f acc x y in
         let* acc, s_list = mapfold2 f acc x_list y_list in
         return (acc, s :: s_list)
      | _ -> None

    let rec mapfold3 f acc x_list y_list z_list =
      match x_list, y_list, z_list with
      | [], [], [] -> return (acc, [])
      | x :: x_list, y :: y_list, z :: z_list ->
         let* acc, s = f acc x y z in
         let* acc, s_list = mapfold3 f acc x_list y_list z_list in
         return (acc, s :: s_list)
      | _ -> None
  end

module State =
  struct
    type ('a, 'state) mon = 'state -> 'a * 'state
                          
    let ret x = fun s -> (x, s)
    let bind f g =
      fun s -> match f s with (a, s') -> g a s'

    let return = ret
    let (let*) = bind
  end

module Misc =
  struct
    let rec mapfold f acc x_list =
      match x_list with
      | [] -> [], acc
      | x :: x_list ->
         let s, acc = f acc x in
         let s_list, acc = mapfold f acc x_list in
         s :: s_list, acc
  end

module Result =
  struct
    open Result
    (* [let* x = e in f x] *)
    let (let*) e f =
      match e with
      | Error(v) -> Error(v)
      | Ok(v) -> f v

    let return v = Ok(v)

    let error v = Error(v)

    let rec map f x_list =
      match x_list with
      | [] -> return []
      | x :: x_list ->
         let* xv = f x in
         let* x_list = map f x_list in
         return (xv :: x_list)

    let rec fold f acc x_list =
      match x_list with
      | [] -> return acc
      | x :: x_list ->
         let* acc = f acc x in
         let* acc = fold f acc x_list in
         return acc

    let rec fold2 with_error f acc x_list y_list =
      match x_list, y_list with
      | [], [] -> return acc
      | x :: x_list, y :: y_list ->
         let* acc = f acc x y in
         let* acc = fold2 with_error f acc x_list y_list in
         return acc
      | _ -> error with_error

    let rec map2 with_error f x_list y_list =
      match x_list, y_list with
      | [], [] -> return []
      | x :: x_list, y :: y_list ->
         let* z = f x y in
         let* z_list = map2 with_error f x_list y_list in
         return (z :: z_list)
      | _ -> error with_error 

    let rec map3 with_error f x_list y_list z_list =
      match x_list, y_list, z_list with
      | [], [], [] -> return []
      | x :: x_list, y :: y_list, z :: z_list ->
         let* t = f x y z in
         let* t_list = map3 with_error f x_list y_list z_list in
         return (t :: t_list)
      | _ -> error with_error 

    let rec mapfold f acc x_list =
      match x_list with
      | [] -> return (acc, [])
      | x :: x_list ->
         let* acc, s = f acc x in
         let* acc, s_list = mapfold f acc x_list in
         return (acc, s :: s_list)

    let rec mapfold2 with_error f acc x_list y_list =
      match x_list, y_list with
      | [], [] -> return (acc, [])
      | x :: x_list, y :: y_list ->
         let* acc, s = f acc x y in
         let* acc, s_list = mapfold2 with_error f acc x_list y_list in
         return (acc, s :: s_list)
      | _ -> error with_error 

    let rec mapfold3 with_error f acc x_list y_list z_list =
      match x_list, y_list, z_list with
      | [], [], [] -> return (acc, [])
      | x :: x_list, y :: y_list, z :: z_list ->
         let* acc, s = f acc x y z in
         let* acc, s_list = mapfold3 with_error f acc x_list y_list z_list in
         return (acc, s :: s_list)
      | _ -> error with_error 
  end
