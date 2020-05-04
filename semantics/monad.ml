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
         let* acc = fold f acc x_list in
         return acc

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
