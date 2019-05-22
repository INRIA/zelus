type 'a t = 'a array array

let create = Array.make_matrix
let get m i j = m.(i).(j)
let set m i j v = m.(i).(j) <- v

let set_row_from_list m i l = m.(i) <- Array.of_list l
