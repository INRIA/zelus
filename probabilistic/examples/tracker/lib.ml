open Owl

let of_lists l = Mat.of_arrays (Array.of_list (List.map Array.of_list l))
let of_list l n m = Mat.of_array (Array.of_list l) n m