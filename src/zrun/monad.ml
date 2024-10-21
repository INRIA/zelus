(***********************************************************************)
(*                                                                     *)
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

module Opt =
  struct
    include Option

    (* [let* x = e in f x] *)
    let (let*) e f =
      match e with
      | None -> None
      | Some(v) -> f v
                 
    let (and*) v1 v2 =
      match v1, v2 with
      | None, _ | _, None -> None
      | Some(v1), Some(v2) -> Some(v1, v2)
                              
    let none = None

    let return v = Some(v)

    let rec map f x_list =
      match x_list with
      | [] -> return []
      | x :: x_list ->
         let* xv = f x in
         let* x_list = map f x_list in
         return (xv :: x_list)

    let rec filter f x_list =
      match x_list with
      | [] -> []
      | x :: x_list ->
         let x = f x in
         match x with
         | None -> filter f x_list
         | Some(x) -> x :: filter f x_list

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

module Mealy =
  struct
                                  
    type 'a state =
      | Sempty : 'a state
      | Sval : 'a -> 'a state
      | Spair : 'a state * 'a state -> 'a state
      
    (* a variation of the state monad. *)
    let ret x s = (Some x, s)
              
    let bind f g s =
      match s with
      | Sempty | Sval _ -> None, s
      | Spair(s1, s2) ->
         let (v1, s1) = f s1 in
         match v1 with
         | None -> None, Spair(s1, s2)
         | Some(v) ->
            let v2, s2 = g v1 s2 in
            v2, Spair (s1, s2)

    let (and*) f1 f2 (s1, s2) =
           let v1, s1 = f1 s1 in
           let v2, s2 = f2 s2 in
           (v1, v2), (s1, s2)
           
    let return = ret
    let (let*) = bind

    (* let rec map f x_list =
      match x_list with
      | [] -> return []
      | x :: x_list ->
         let* xv = f x in
         let* x_list = map f x_list in
         return (xv :: x_list) *)

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
    include Result
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

    let rec seqfold f acc x_seq =
      match x_seq () with
      | Seq.Nil -> return acc
      | Seq.Cons(x, x_seq) ->
         let* acc = f acc x in
         seqfold f acc x_seq

    let rec fold2 when_error f acc x_list y_list =
      match x_list, y_list with
      | [], [] -> return acc
      | x :: x_list, y :: y_list ->
         let* acc = f acc x y in
         let* acc = fold2 when_error f acc x_list y_list in
         return acc
      | _ -> error when_error

    let rec map2 with_error f x_list y_list =
      match x_list, y_list with
      | [], [] -> return []
      | x :: x_list, y :: y_list ->
         let* z = f x y in
         let* z_list = map2 with_error f x_list y_list in
         return (z :: z_list)
      | _ -> error with_error 

    let rec map3 when_error f x_list y_list z_list =
      match x_list, y_list, z_list with
      | [], [], [] -> return []
      | x :: x_list, y :: y_list, z :: z_list ->
         let* t = f x y z in
         let* t_list = map3 when_error f x_list y_list z_list in
         return (t :: t_list)
      | _ -> error when_error 

    let rec mapfold f acc x_list =
      match x_list with
      | [] -> return (acc, [])
      | x :: x_list ->
         let* acc, s = f acc x in
         let* acc, s_list = mapfold f acc x_list in
         return (acc, s :: s_list)

    let rec mapfold2 when_error f acc x_list y_list =
      match x_list, y_list with
      | [], [] -> return (acc, [])
      | x :: x_list, y :: y_list ->
         let* acc, s = f acc x y in
         let* acc, s_list = mapfold2 when_error f acc x_list y_list in
         return (acc, s :: s_list)
      | _ -> error when_error 

    let rec mapfold3 when_error f acc x_list y_list z_list =
      match x_list, y_list, z_list with
      | [], [], [] -> return (acc, [])
      | x :: x_list, y :: y_list, z :: z_list ->
         let* acc, s = f acc x y z in
         let* acc, s_list = mapfold3 when_error f acc x_list y_list z_list in
         return (acc, s :: s_list)
      | _ -> error when_error 
  end
