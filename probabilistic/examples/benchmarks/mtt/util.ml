open Owl

let tdiff = 1.0

let list_init = List.init

let birth_rate =  0.1
let death_rate = 0.02

let p_dead = exp (-. tdiff *. death_rate)

let lambda_new = birth_rate *. tdiff

let mu_new = 
  Mat.of_arrays [| [| 0.; |];
                   [| 0.; |];
                   [| 0.; |];
                   [| 0.; |]; |]

let sigma_new = 
  Mat.of_arrays [| [| 1.0; 0.0; 0.0; 0.0; |];
                   [| 0.0; 1.0; 0.0; 0.0; |];
                   [| 0.0; 0.0; 0.001; 0.0; |];
                   [| 0.0; 0.0; 0.0; 0.001; |]; |]

let a_u = 
  Mat.of_arrays [| [| 1.0; 0.0; tdiff; 0.0 |];
                   [| 0.0; 1.0; 0.0; tdiff |];
                   [| 0.0; 0.0; 1.0; 0.0   |];          
                   [| 0.0; 0.0; 0.0; 1.0   |]; |]

let b_u = 
  Mat.of_arrays [| [| 0.; |];
                   [| 0.; |]; 
                   [| 0.; |]; 
                   [| 0.; |]; |]

let sigma_update = 
  Mat.of_arrays [| [| 0.01; 0.0; 0.0; 0.0 |];
                   [| 0.0; 0.01; 0.0; 0.0 |];
                   [| 0.0; 0.0;  0.1; 0.0 |];
                   [| 0.0; 0.0;  0.0; 0.1 |]; |]

let lambda_clutter = 1.

let mu_clutter = 
  Mat.of_arrays [| [| 0.; |];
                   [| 0.; |]; |]

let proj_pos =
  Mat.of_arrays [| [| 1.0; 0.0; 0.0; 0.0 |];
                   [| 0.0; 1.0; 0.0; 0.0 |]; |]

let sigma_obs =
  Mat.of_arrays [| [| 1.0; 0.0 |];
                   [| 0.0; 1.0 |]; |]

let sigma_clutter = 
  Mat.of_arrays [| [| 10.0; 0.0 |];
                   [| 0.0; 10.0 |]; |]

let shuffle x = 
  let arr = Array.of_list x in
  for n = Array.length arr - 1 downto 1 do
    let k = Random.int (n + 1) in
    let tmp = arr.(n) in
    arr.(n) <- arr.(k);
    arr.(k) <- tmp
  done;
  Array.to_list arr

let ( *@ ) = Mat.( *@ )
let ( +@ ) = Mat.add

let string_of_vec2_list vec_lst =
  "[" ^
  String.concat "," (List.map (fun vec ->
    "(" ^ string_of_float (Mat.get vec 0 0) ^ ", " ^ 
    string_of_float (Mat.get vec 1 0) ^ ")"
  ) vec_lst)
  ^ "]" 
