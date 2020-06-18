(* vec is an ordered float array
 * returns i such that vec.(i) < v < vec.(i+1) (or i = 0 or i = length vec) *)
let ifind v vec =
  let rec aux start_i end_i =
    if start_i = end_i then start_i
    else
      let i = (start_i + end_i) / 2 in
      let v_i = vec.(i) in
      let v_ip1 = vec.(i+1) in
      if v_i <= v && v < v_ip1 then i
      else if v_i > v then aux start_i (max 0 (i-1))
      else if v >= v_ip1 then
        aux (min (Array.length vec - 1) (i+1)) end_i
      else assert false
  in if v < vec.(0) then 0
  else if v > vec.(Array.length vec - 1) then Array.length vec
  else (aux 0 (Array.length vec - 1)) + 1

(* linear interpolatiion, x1 <= xi <= x2 *)
let interp x1 x2 val1 val2 xi =
  if val1 = val2 then val1
  else
  (x2 -. xi) /. (x2 -. x1) *. val1 +.
  (xi -. x1) /. (x2 -. x1) *. val2

(* linear extrapolation, x1 <= x2 <= xi OR xi <= x1 <= x2 *)
let extrap x1 x2 val1 val2 xi =
  let slope = (val2 -. val1) /. (x2 -. x1) in
  let dif = slope *. (xi -. x1) in
  val1 +. dif

(* LOOKUP FUNCTIONS:
 * These functions implement lookup tables that performs linear interpolation
 * and extrapolation. *)

let interp1 (line, vals) =
  fun l ->
  try
    let li = ifind l line in
    if li = 0 then
      extrap line.(0) line.(1) vals.(0) vals.(1) l
    else if li = (Array.length line) then
      extrap line.(li - 2) line.(li - 1) vals.(li - 2) vals.(li - 1) l
    else
      interp line.(li - 1) line.(li) vals.(li - 1) vals.(li) l
  with Invalid_argument s ->
    let li = ifind l line in
    print_string "Invalid argument (interp1): "; print_string s;
    print_newline ();
    print_int li; print_string " / "; print_int (Array.length line);
    print_string ", "; print_float l; print_newline ();
    exit 1
