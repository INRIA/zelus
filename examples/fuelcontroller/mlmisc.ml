
let input_line ins =
    try input_line ins
    with End_of_file -> "0.0"

let print_float = Printf.printf "%.12f"

let rec print_floats l = match l with
    []  -> print_newline ()
  | [x] -> print_float x; print_newline ()
  | (x::xs) -> print_float x; print_string "\t"; print_floats xs

let rec print_floats_5 f1 f2 f3 f4 f5 =
  Printf.printf "%e\t%e\t%e\t%e\t%e\n" f1 f2 f3 f4 f5

let rec print_floats_4 f1 f2 f3 f4 =
  Printf.printf "%e\t%e\t%e\t%e\n" f1 f2 f3 f4

let rec print_floats_2 f1 f2 =
  Printf.printf "%e\t%e\n" f1 f2
  
type ('x, 'y) lookup = 'x * 'y -> float

let make_lookup (bpl1, bps1) (bpl2, bps2) table =
  Lookup.float_make_lookup_2d
  bpl1
  bpl2
  (Lookup.LinearInterpolation false)
  (Lookup.LinearInterpolation false)
  bps1
  bps2
  table
  (fun y -> y)

let use_lookup lup x = lup x

