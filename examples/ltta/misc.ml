(* Random generator *)
let rand_val min max =
  (Random.float (max -. min)) +. min

(* Queue API *)
let empty () = []
let front l = print_endline "pop"; List.hd (List.rev l)
let dequeue l = print_endline "tail";  List.tl l
let enqueue l i = print_endline "push"; i::l
let sum l = List.fold_left (+.) 0.0 l
let is_empty l = (l == [])
