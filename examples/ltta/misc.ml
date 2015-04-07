(* Random generator *)
let arbitrary min max =
  (max +. min) /. 2.
  (* (Random.float (max -. min)) +. min *)

(* Queue API *)
let empty () = []
let front l = List.hd (List.rev l)
let dequeue l = List.tl l
let enqueue l i = i::l
let sum l = List.fold_left (+.) 0.0 l
let is_empty l = (l == [])

(* Print *)
let print o1 o2 = Format.printf "o1 = %d, o2 = %d\n" o1 o2
